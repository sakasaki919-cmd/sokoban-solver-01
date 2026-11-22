// Sokoban push solver for make.fun sokoban-solver-01-run-20261121.
//
// The levels are built from rooms: a hallway with 1-4 small rooms off it,
// each room holding 3-4 boxes whose goals are its own. A box never leaves
// its room, so the rooms are independent problems and the level optimum is
// the sum of the rooms' optima. Searching the whole level at once meets the
// product of the rooms' positions, which is why a plain search stalls.
//
// So this solver works room by room:
//   1. Cut the dead squares of the player's row (the hallway: a box there
//      reaches no goal) out of the floor; each remaining connected part
//      holding a box is a room.
//   2. Solve each room on its own with a breadth-first search over pushes
//      (every push costs 1, so the first solved state is push-optimal),
//      the other rooms' boxes standing as walls, the player walking on
//      from where the last room left it.
//   3. Concatenate the rooms' moves. The total pushes equal P*.
//
// Deadlocks are pruned two ways: static dead squares (reverse-pull analysis
// from the goals) and frozen 2x2 blocks of walls and boxes. A state is the
// boxes plus the player's reachable region, named by its lowest square.
//
// If a level is not a set of rooms, fall back to a push-based A* over the
// whole level (same deadlock pruning, optimal box-to-goal assignment
// heuristic). Deterministic: every budget is a state/expansion count, never
// wall-clock time. No network, no randomness. Node 22, standard library
// only, erasable TypeScript syntax.

import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// State budgets (deterministic; the whole set shares one wall of 60 s).
const ROOM_STATE_BUDGET = 250000;
const ASTAR_TOTAL_BUDGET = 120000;
const ASTAR_PER_LEVEL_CAP = 60000;
const GREEDY_BUDGET = 40000;
const BIG = 1e6;

interface Dir { dx: number; dy: number; ch: string }
const DIRS: Dir[] = [
  { dx: 0, dy: -1, ch: 'u' },
  { dx: 0, dy: 1, ch: 'd' },
  { dx: -1, dy: 0, ch: 'l' },
  { dx: 1, dy: 0, ch: 'r' },
];

// ---------------------------------------------------------------------------
// Level
// ---------------------------------------------------------------------------

interface Level {
  w: number;
  h: number;
  wall: Uint8Array; // 1 = wall
  goalSet: Uint8Array; // 1 = goal
  goals: number[];
  boxes: number[]; // sorted
  player: number;
}

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goalSet = new Uint8Array(w * h);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = 0;
  rows.forEach((row, y) => {
    for (let x = 0; x < w; x++) {
      const ch = row[x] ?? '#';
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') { goalSet[i] = 1; goals.push(i); }
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goalSet, goals, boxes, player };
}

// ---------------------------------------------------------------------------
// Static analysis: BFS distances from each goal, and dead squares.
// A square is dead when a box on it can never reach a goal. Reverse-pull
// analysis: from a live square t, a box at s = t - d can be pushed to t only
// when the player can stand at s - d, so s is live when s is free and s - d
// is free. Squares never reached are dead. (Goals are live by definition.)
// ---------------------------------------------------------------------------

interface StaticInfo {
  // dist[g][s]: BFS distance from goals[g] to square s through free cells.
  dist: number[][];
  dead: Uint8Array; // 1 = a box here can never reach a goal
}

function computeStatic(level: Level): StaticInfo {
  const { w, h, wall, goals } = level;
  const size = w * h;
  const dist: number[][] = [];
  const seen = new Int32Array(size);
  for (let gi = 0; gi < goals.length; gi++) {
    const d = new Array<number>(size).fill(BIG);
    const q: number[] = [goals[gi]!];
    d[goals[gi]!] = 0;
    seen[goals[gi]!] = gi + 1;
    for (let qi = 0; qi < q.length; qi++) {
      const cur = q[qi]!;
      const cx = cur % w;
      const cy = Math.floor(cur / w);
      for (const dir of DIRS) {
        const nx = cx + dir.dx;
        const ny = cy + dir.dy;
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const ni = ny * w + nx;
        if (wall[ni] || seen[ni] === gi + 1) continue;
        seen[ni] = gi + 1;
        d[ni] = d[cur]! + 1;
        q.push(ni);
      }
    }
    dist.push(d);
  }
  // Reverse-pull liveness.
  const live = new Uint8Array(size);
  const queue: number[] = [];
  for (const g of goals) { live[g] = 1; queue.push(g); }
  for (let qi = 0; qi < queue.length; qi++) {
    const t = queue[qi]!;
    const tx = t % w;
    const ty = Math.floor(t / w);
    for (const dir of DIRS) {
      const sx = tx - dir.dx;
      const sy = ty - dir.dy;
      if (sx < 0 || sx >= w || sy < 0 || sy >= h) continue;
      const s = sy * w + sx;
      if (wall[s] || live[s]) continue;
      // The player must stand at s - d.
      const bx = sx - dir.dx;
      const by = sy - dir.dy;
      if (bx < 0 || bx >= w || by < 0 || by >= h) continue;
      if (wall[by * w + bx]) continue;
      live[s] = 1;
      queue.push(s);
    }
  }
  const dead = new Uint8Array(size);
  for (let i = 0; i < size; i++) if (!wall[i] && !live[i]) dead[i] = 1;
  return { dist, dead };
}

// ---------------------------------------------------------------------------
// Shared helpers: flood fill, 2x2 deadlock, move reconstruction.
// ---------------------------------------------------------------------------

// Flood fill from `start` through free cells (not wall, not box). Returns the
// region and its smallest cell index (the canonical player position).
function flood(level: Level, boxSet: Uint8Array, start: number): { region: Uint8Array; canon: number } {
  const { w, h, wall } = level;
  const region = new Uint8Array(w * h);
  const q: number[] = [start];
  region[start] = 1;
  let canon = start;
  for (let qi = 0; qi < q.length; qi++) {
    const cur = q[qi]!;
    if (cur < canon) canon = cur;
    const cx = cur % w;
    const cy = Math.floor(cur / w);
    for (const dir of DIRS) {
      const nx = cx + dir.dx;
      const ny = cy + dir.dy;
      if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
      const ni = ny * w + nx;
      if (wall[ni] || boxSet[ni] || region[ni]) continue;
      region[ni] = 1;
      q.push(ni);
    }
  }
  return { region, canon };
}

// A 2x2 block of boxes/walls with a box and no goal is frozen: no box in it
// can ever be pushed out. Only blocks containing cell `p` can be new.
function has2x2Deadlock(level: Level, boxSet: Uint8Array, p: number): boolean {
  const { w, h, wall, goalSet } = level;
  const px = p % w;
  const py = Math.floor(p / w);
  for (let ox = -1; ox <= 0; ox++) {
    for (let oy = -1; oy <= 0; oy++) {
      const x0 = px + ox;
      const y0 = py + oy;
      if (x0 < 0 || y0 < 0 || x0 + 1 >= w || y0 + 1 >= h) continue;
      const cells = [
        y0 * w + x0, y0 * w + x0 + 1,
        (y0 + 1) * w + x0, (y0 + 1) * w + x0 + 1,
      ];
      let hasBox = false;
      let hasGoal = false;
      let allBlocked = true;
      for (const c of cells) {
        if (goalSet[c]) hasGoal = true;
        if (boxSet[c]) hasBox = true;
        if (!wall[c] && !boxSet[c]) allBlocked = false;
      }
      if (allBlocked && hasBox && !hasGoal) return true;
    }
  }
  return false;
}

function isSolved(level: Level, boxes: number[]): boolean {
  for (const b of boxes) if (!level.goalSet[b]) return false;
  return true;
}

// Replay a push list from the start, walking the player to each push with
// BFS, and emit the full move string (lowercase; the checker replays by
// position, so case carries no meaning).
function toMoves(level: Level, pushes: Array<{ from: number; dir: number }>): string {
  const { w, h, wall } = level;
  const boxes = level.boxes.slice();
  const boxSet = new Uint8Array(w * h);
  for (const b of boxes) boxSet[b] = 1;
  let player = level.player;
  let out = '';
  const walk = (from: number, to: number): string | null => {
    if (from === to) return '';
    const prev = new Int32Array(w * h).fill(-1);
    const prevDir = new Int8Array(w * h).fill(-1);
    const q: number[] = [from];
    prev[from] = from;
    for (let qi = 0; qi < q.length; qi++) {
      const cur = q[qi]!;
      if (cur === to) break;
      const cx = cur % w;
      const cy = Math.floor(cur / w);
      for (let di = 0; di < 4; di++) {
        const dir = DIRS[di]!;
        const nx = cx + dir.dx;
        const ny = cy + dir.dy;
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const ni = ny * w + nx;
        if (wall[ni] || boxSet[ni] || prev[ni] !== -1) continue;
        prev[ni] = cur;
        prevDir[ni] = di;
        q.push(ni);
      }
    }
    if (prev[to] === -1) return null;
    let s = '';
    for (let cur = to; cur !== from; cur = prev[cur]!) s = DIRS[prevDir[cur]!]!.ch + s;
    return s;
  };
  for (const p of pushes) {
    const dir = DIRS[p.dir]!;
    const behind = p.from - (dir.dy * w + dir.dx);
    const wlk = walk(player, behind);
    if (wlk === null) return '';
    out += wlk;
    out += dir.ch;
    const bi = boxes.indexOf(p.from);
    const target = p.from + (dir.dy * w + dir.dx);
    boxSet[p.from] = 0;
    boxSet[target] = 1;
    boxes[bi] = target;
    boxes.sort((a, b) => a - b);
    player = p.from;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Rooms: cut the dead squares of the player's row (the hallway) out of the
// floor; each remaining connected part holding a box is a room. Null when the
// level is no set of rooms (a box starts in the hallway, or some part holds
// more or fewer boxes than goals).
// ---------------------------------------------------------------------------

interface Room {
  boxes: number[];
  goals: number[];
  done: boolean;
}

function roomsOf(level: Level, st: StaticInfo): Room[] | null {
  const { w, h, wall, goals, boxes, player } = level;
  const row = Math.floor(player / w);
  const cut = new Uint8Array(w * h);
  for (let i = row * w; i < (row + 1) * w; i++) {
    if (!wall[i] && st.dead[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(w * h).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < w * h; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares: number[] = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      const cur = squares[i]!;
      const cx = cur % w;
      const cy = Math.floor(cur / w);
      for (const dir of DIRS) {
        const nx = cx + dir.dx;
        const ny = cy + dir.dy;
        if (nx < 0 || nx >= w || ny < 0 || ny >= h) continue;
        const ni = ny * w + nx;
        if (!wall[ni] && !cut[ni] && part[ni] < 0) {
          part[ni] = rooms.length;
          squares.push(ni);
        }
      }
    }
    rooms.push({ boxes: [], goals: [], done: false });
  }
  for (const b of boxes) {
    if (part[b] < 0) return null;
    rooms[part[b]]!.boxes.push(b);
  }
  for (const g of goals) {
    if (part[g] < 0) return null;
    rooms[part[g]]!.goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

// ---------------------------------------------------------------------------
// Room solver: breadth-first search over pushes. Every push costs 1, so the
// first solved state dequeued is push-optimal. States are keyed by the
// region's lowest square and the boxes, packed as a base-`size` number
// (exact while size^(boxes+1) stays under 2^53; a room holds few boxes).
// ---------------------------------------------------------------------------

function solveRoomBFS(level: Level, st: StaticInfo, maxStates: number): { pushes: number; moves: string } | null {
  const { w, h, wall, goalSet } = level;
  const size = w * h;
  const keyOf = (boxes: number[], low: number): number => {
    let k = low;
    for (const b of boxes) k = k * size + b;
    return k;
  };
  if (isSolved(level, level.boxes)) return { pushes: 0, moves: '' };
  if (level.boxes.some((b) => st.dead[b])) return null;
  const sBoxes: number[][] = [level.boxes.slice()];
  const sPlayer: number[] = [level.player];
  const sParent: number[] = [-1];
  const sPushFrom: number[] = [-1];
  const sPushDir: number[] = [-1];
  const seen = new Map<number, number>();
  const boxSet = new Uint8Array(size);
  for (const b of level.boxes) boxSet[b] = 1;
  const { canon } = flood(level, boxSet, level.player);
  seen.set(keyOf(level.boxes, canon), 0);
  let head = 0;
  while (head < sBoxes.length) {
    if (sBoxes.length >= maxStates) return null;
    const s = head++;
    const boxes = sBoxes[s]!;
    boxSet.fill(0);
    for (const b of boxes) boxSet[b] = 1;
    const { region } = flood(level, boxSet, sPlayer[s]!);
    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi]!;
      const bx = b % w;
      const by = Math.floor(b / w);
      for (let di = 0; di < 4; di++) {
        const dir = DIRS[di]!;
        const tx = bx + dir.dx;
        const ty = by + dir.dy;
        if (tx < 0 || tx >= w || ty < 0 || ty >= h) continue;
        const target = ty * w + tx;
        if (wall[target] || boxSet[target]) continue;
        const px = bx - dir.dx;
        const py = by - dir.dy;
        if (px < 0 || px >= w || py < 0 || py >= h) continue;
        if (!region[py * w + px]) continue;
        if (st.dead[target]) continue;
        const nb = boxes.slice();
        nb[bi] = target;
        nb.sort((x, y) => x - y);
        // Solved on this push: no deadlock test or flood is needed for a
        // successor that ends the search. The pushed box must have landed
        // on a goal (every other box is unchanged), a goal is never dead,
        // and no 2x2 block holding a goal is frozen, so both tests below
        // would answer false; record the state and return straight away.
        // (A solved state can never already be in `seen`: the first solved
        // state generated returns at once, so none is ever recorded.)
        if (isSolved(level, nb)) {
          const idx = sBoxes.length;
          sBoxes.push(nb);
          sPlayer.push(b);
          sParent.push(s);
          sPushFrom.push(b);
          sPushDir.push(di);
          const pushes: Array<{ from: number; dir: number }> = [];
          for (let t = idx; t > 0; t = sParent[t]!) {
            pushes.push({ from: sPushFrom[t]!, dir: sPushDir[t]! });
          }
          pushes.reverse();
          const moves = toMoves(level, pushes);
          if (moves === '' && pushes.length > 0) return null;
          return { pushes: pushes.length, moves };
        }
        boxSet[b] = 0;
        boxSet[target] = 1;
        // A box pushed onto a goal can never complete a frozen 2x2 block:
        // every 2x2 block holding the box also holds that goal, so the
        // deadlock test would answer false. Skip the test outright.
        const frozen = goalSet[target] ? false : has2x2Deadlock(level, boxSet, target);
        let canon2 = -1;
        if (!frozen) {
          const r2 = flood(level, boxSet, b);
          canon2 = r2.canon;
        }
        boxSet[target] = 0;
        boxSet[b] = 1;
        if (frozen) continue;
        const key = keyOf(nb, canon2);
        if (seen.has(key)) continue;
        const idx = sBoxes.length;
        seen.set(key, idx);
        sBoxes.push(nb);
        sPlayer.push(b);
        sParent.push(s);
        sPushFrom.push(b);
        sPushDir.push(di);
        if (isSolved(level, nb)) {
          const pushes: Array<{ from: number; dir: number }> = [];
          for (let t = idx; t > 0; t = sParent[t]!) {
            pushes.push({ from: sPushFrom[t]!, dir: sPushDir[t]! });
          }
          pushes.reverse();
          const moves = toMoves(level, pushes);
          if (moves === '' && pushes.length > 0) return null;
          return { pushes: pushes.length, moves };
        }
      }
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// Solve a level room by room: each room's push-optimal solution in turn,
// the other rooms' boxes standing as walls (on their goals once their room
// is done), the player walking on from where the last room left it.
// ---------------------------------------------------------------------------

function solveByRooms(level: Level, st: StaticInfo): { pushes: number; moves: string } | null {
  const rooms = roomsOf(level, st);
  if (rooms === null) return null;
  let player = level.player;
  let pushes = 0;
  let moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = {
      w: level.w, h: level.h, wall,
      goalSet: level.goalSet,
      goals: room.goals.slice().sort((a, b) => a - b),
      boxes: room.boxes.slice().sort((a, b) => a - b),
      player,
    };
    const solved = solveRoomBFS(sub, st, ROOM_STATE_BUDGET);
    if (solved === null) return null;
    pushes += solved.pushes;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    room.done = true;
  }
  return { pushes, moves };
}

// The square the player stands on after `moves` (case aside) from `from`.
function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) {
    p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  }
  return p;
}

// ---------------------------------------------------------------------------
// Fallback: push-based A* over the whole level (used only when a level is
// no set of rooms). Heuristic: optimal box->goal assignment (Hungarian)
// for few boxes, else the sum of nearest-goal distances; both lower bounds.
// ---------------------------------------------------------------------------

function hungarian(a: number[][]): number {
  const n = a.length;
  if (n === 0) return 0;
  const u = new Array<number>(n + 1).fill(0);
  const v = new Array<number>(n + 1).fill(0);
  const p = new Array<number>(n + 1).fill(0);
  const way = new Array<number>(n + 1).fill(0);
  for (let i = 1; i <= n; i++) {
    p[0] = i;
    let j0 = 0;
    const minv = new Array<number>(n + 1).fill(Infinity);
    const used = new Array<boolean>(n + 1).fill(false);
    do {
      used[j0] = true;
      const i0 = p[j0]!;
      let delta = Infinity;
      let j1 = 0;
      for (let j = 1; j <= n; j++) {
        if (used[j]) continue;
        const cur = a[i0 - 1]![j - 1]! - u[i0]! - v[j]!;
        if (cur < minv[j]!) { minv[j] = cur; way[j] = j0; }
        if (minv[j]! < delta) { delta = minv[j]!; j1 = j; }
      }
      for (let j = 0; j <= n; j++) {
        if (used[j]) { u[p[j]!]! += delta; v[j]! -= delta; }
        else minv[j]! -= delta;
      }
      j0 = j1;
    } while (p[j0] !== 0);
    do {
      const j1 = way[j0]!;
      p[j0] = p[j1]!;
      j0 = j1;
    } while (j0 !== 0);
  }
  return -v[0]!;
}

interface ASolver {
  level: Level;
  st: StaticInfo;
  sBoxes: number[][];
  sPlayer: number[];
  sG: number[];
  sF: number[];
  sParent: number[];
  sPushFrom: number[];
  sPushDir: number[];
  best: Map<string, number>;
  hCache: Map<string, number>;
  boxSet: Uint8Array;
}

function aHeuristic(sv: ASolver, boxes: number[]): number {
  const key = boxes.join(',');
  const cached = sv.hCache.get(key);
  if (cached !== undefined) return cached;
  const { st, level } = sv;
  let h = 0;
  if (boxes.length <= 8) {
    const remBoxes: number[] = [];
    const usedGoal = new Uint8Array(level.goals.length);
    for (const b of boxes) {
      const gi = level.goals.indexOf(b);
      if (gi >= 0 && level.goalSet[b]) usedGoal[gi] = 1;
      else remBoxes.push(b);
    }
    const remGoals: number[] = [];
    for (let gi = 0; gi < level.goals.length; gi++) if (!usedGoal[gi]) remGoals.push(gi);
    if (remBoxes.length > 0) {
      const n = remBoxes.length;
      const cost: number[][] = [];
      for (let i = 0; i < n; i++) {
        const row: number[] = [];
        for (let j = 0; j < n; j++) {
          const d = st.dist[remGoals[j]!]![remBoxes[i]!]!;
          row.push(d >= BIG ? BIG : d);
        }
        cost.push(row);
      }
      h = hungarian(cost);
    }
  } else {
    for (const b of boxes) {
      let best = BIG;
      for (let gi = 0; gi < level.goals.length; gi++) {
        const d = st.dist[gi]![b]!;
        if (d < best) best = d;
      }
      h += best;
      if (h >= BIG) break;
    }
  }
  if (h >= BIG) h = BIG;
  sv.hCache.set(key, h);
  return h;
}

function aKey(boxes: number[], player: number): string {
  return boxes.join(',') + '|' + player;
}

class AHeap {
  private a: number[] = [];
  private sv: ASolver;
  private greedy: boolean;
  constructor(sv: ASolver, greedy: boolean) {
    this.sv = sv;
    this.greedy = greedy;
  }
  get size(): number { return this.a.length; }
  private less(x: number, y: number): boolean {
    const sv = this.sv;
    if (sv.sF[x] !== sv.sF[y]) return sv.sF[x]! < sv.sF[y]!;
    if (sv.sG[x] !== sv.sG[y]) return sv.sG[x]! > sv.sG[y]!;
    return x < y;
  }
  push(idx: number): void {
    const a = this.a;
    a.push(idx);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!this.less(a[i]!, a[p]!)) break;
      const t = a[i]!; a[i] = a[p]!; a[p] = t;
      i = p;
    }
  }
  pop(): number {
    const a = this.a;
    const top = a[0]!;
    const last = a.pop()!;
    if (a.length > 0) {
      a[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= a.length) break;
        if (c + 1 < a.length && this.less(a[c + 1]!, a[c]!)) c++;
        if (!this.less(a[c]!, a[i]!)) break;
        const t = a[i]!; a[i] = a[c]!; a[c] = t;
        i = c;
      }
    }
    return top;
  }
}

function aExpand(sv: ASolver, heap: AHeap, s: number, greedy: boolean): void {
  const level = sv.level;
  const { w, h, wall } = level;
  const boxes = sv.sBoxes[s]!;
  const boxSet = sv.boxSet;
  boxSet.fill(0);
  for (const b of boxes) boxSet[b] = 1;
  const { region } = flood(level, boxSet, sv.sPlayer[s]!);
  for (let bi = 0; bi < boxes.length; bi++) {
    const b = boxes[bi]!;
    const bx = b % w;
    const by = Math.floor(b / w);
    for (let di = 0; di < 4; di++) {
      const dir = DIRS[di]!;
      const tx = bx + dir.dx;
      const ty = by + dir.dy;
      if (tx < 0 || tx >= w || ty < 0 || ty >= h) continue;
      const target = ty * w + tx;
      if (wall[target] || boxSet[target]) continue;
      const px = bx - dir.dx;
      const py = by - dir.dy;
      if (px < 0 || px >= w || py < 0 || py >= h) continue;
      if (!region[py * w + px]) continue;
      if (sv.st.dead[target]) continue;
      const nb = boxes.slice();
      nb[bi] = target;
      nb.sort((x, y) => x - y);
      boxSet[b] = 0;
      boxSet[target] = 1;
      const dead2 = has2x2Deadlock(level, boxSet, target);
      let canon = -1;
      if (!dead2) canon = flood(level, boxSet, b).canon;
      boxSet[target] = 0;
      boxSet[b] = 1;
      if (dead2) continue;
      const g2 = sv.sG[s]! + 1;
      const key = aKey(nb, canon);
      const prev = sv.best.get(key);
      if (prev !== undefined && sv.sG[prev]! <= g2) continue;
      const h2 = aHeuristic(sv, nb);
      if (h2 >= BIG) continue;
      const idx = sv.sBoxes.length;
      sv.sBoxes.push(nb);
      sv.sPlayer.push(canon);
      sv.sG.push(g2);
      sv.sF.push(greedy ? h2 : g2 + h2);
      sv.sParent.push(s);
      sv.sPushFrom.push(b);
      sv.sPushDir.push(di);
      sv.best.set(key, idx);
      heap.push(idx);
    }
  }
}

function aSearch(level: Level, st: StaticInfo, budget: number, greedy: boolean): { pushes: Array<{ from: number; dir: number }>; expansions: number } | null {
  const sv: ASolver = {
    level, st,
    sBoxes: [], sPlayer: [], sG: [], sF: [], sParent: [], sPushFrom: [], sPushDir: [],
    best: new Map(), hCache: new Map(), boxSet: new Uint8Array(level.w * level.h),
  };
  const boxSet = sv.boxSet;
  for (const b of level.boxes) boxSet[b] = 1;
  const { canon } = flood(level, boxSet, level.player);
  const h0 = aHeuristic(sv, level.boxes);
  if (h0 >= BIG) return null;
  const heap = new AHeap(sv, greedy);
  const root = 0;
  sv.sBoxes.push(level.boxes.slice());
  sv.sPlayer.push(canon);
  sv.sG.push(0);
  sv.sF.push(h0);
  sv.sParent.push(-1);
  sv.sPushFrom.push(-1);
  sv.sPushDir.push(-1);
  sv.best.set(aKey(level.boxes, canon), root);
  heap.push(root);
  let expansions = 0;
  while (heap.size > 0 && expansions < budget) {
    const s = heap.pop();
    if (sv.best.get(aKey(sv.sBoxes[s]!, sv.sPlayer[s]!)) !== s) continue;
    if (isSolved(level, sv.sBoxes[s]!)) {
      const pushes: Array<{ from: number; dir: number }> = [];
      for (let t = s; t > 0; t = sv.sParent[t]!) {
        pushes.push({ from: sv.sPushFrom[t]!, dir: sv.sPushDir[t]! });
      }
      pushes.reverse();
      return { pushes, expansions };
    }
    expansions++;
    aExpand(sv, heap, s, greedy);
  }
  return null;
}

// ---------------------------------------------------------------------------
// Solve one level: rooms first, whole-level A* (then greedy) as fallback.
// ---------------------------------------------------------------------------

function solve(text: string, budget: number): { moves: string; pushes: number; expansions: number; solved: boolean } {
  const level = parseLevel(text);
  const st = computeStatic(level);
  const empty = { moves: '', pushes: 0, expansions: 0, solved: false };
  if (isSolved(level, level.boxes)) return { moves: '', pushes: 0, expansions: 0, solved: true };
  const byRooms = solveByRooms(level, st);
  if (byRooms !== null) {
    return { moves: byRooms.moves, pushes: byRooms.pushes, expansions: 0, solved: true };
  }
  const a = aSearch(level, st, budget, false);
  if (a !== null) {
    const moves = toMoves(level, a.pushes);
    if (moves !== '' || a.pushes.length === 0) {
      return { moves, pushes: a.pushes.length, expansions: a.expansions, solved: true };
    }
  }
  const g = aSearch(level, st, GREEDY_BUDGET, true);
  if (g !== null) {
    const moves = toMoves(level, g.pushes);
    if (moves !== '' || g.pushes.length === 0) {
      return { moves, pushes: g.pushes.length, expansions: a !== null ? a.expansions : 0, solved: true };
    }
  }
  return empty;
}

// ---------------------------------------------------------------------------
// Driver: one run answers every instance under /input/<id>/level.txt.
// ---------------------------------------------------------------------------

let remaining = ASTAR_TOTAL_BUDGET;
const ids = readdirSync(I).sort().filter((id) => {
  try { return statSync(join(I, id)).isDirectory(); } catch { return false; }
});
for (const id of ids) {
  let levelText = '';
  try { levelText = readFileSync(join(I, id, 'level.txt'), 'utf8'); } catch { levelText = ''; }
  const budget = Math.min(ASTAR_PER_LEVEL_CAP, remaining);
  const r = levelText === '' ? { moves: '', pushes: 0, expansions: 0, solved: false } : solve(levelText, budget);
  remaining = Math.max(0, remaining - r.expansions);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${r.moves}\n`);
}
