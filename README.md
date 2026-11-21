# Sokoban Push Solver — make.fun

[![make.fun · sokoban-solver-01-run-20261121](https://make.fun/badge/sokoban-solver-01-run-20261121.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![rank](https://make.fun/badge/sokoban-solver-01-run-20261121/sakasaki919-cmd/sokoban-solver-01/rank.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)
[![reward](https://make.fun/badge/sokoban-solver-01-run-20261121/sakasaki919-cmd/sokoban-solver-01/reward.svg)](https://make.fun/bounty/sokoban-solver-01-run-20261121?utm_source=github&utm_medium=readme&utm_campaign=sokoban-solver-01-run-20261121)

Entry for the [make.fun](https://make.fun) bounty [sokoban-solver-01-run-20261121](https://make.fun/bounty/sokoban-solver-01-run-20261121) — "Build the best Sokoban solver".

## Approach

The levels are built from rooms: a hallway with 1–4 small rooms off it, each
room holding 3–4 boxes whose goals are its own. A box never leaves its room,
so the rooms are independent problems and the level optimum is the sum of the
rooms' optima. Searching the whole level at once meets the product of the
rooms' positions, which is why a plain search stalls.

This solver works room by room:

1. **Find the rooms.** Cut the dead squares of the player's row (the hallway:
   a box there reaches no goal) out of the floor; each remaining connected
   part holding a box is a room.
2. **Solve each room on its own** with a breadth-first search over pushes
   (every push costs 1, so the first solved state is push-optimal), the other
   rooms' boxes standing as walls, the player walking on from where the last
   room left it.
3. **Concatenate the rooms' moves.** Total pushes equal P\*.

Deadlocks are pruned two ways: static dead squares (reverse-pull analysis
from the goals) and frozen 2×2 blocks of walls and boxes. A state is the
boxes plus the player's reachable region, named by its lowest square.

If a level is not a set of rooms, it falls back to a push-based A\* over the
whole level (same deadlock pruning, optimal box-to-goal assignment heuristic).

## Practice results

| instance | boxes | pushes | P\* | points |
|----------|-------|--------|-----|--------|
| i001 | 3 | 13 | 13 | 1000 |
| i002 | 4 | 16 | 16 | 1000 |
| i003 | 8 | 29 | 29 | 1000 |
| i004 | 12 | 47 | 47 | 1000 |
| i005 | 16 | 60 | 60 | 1000 |

Score **1,000,000 / 1,000,000** in ~2 seconds (limit 60 s), deterministic
(two runs byte-identical).

## Run

```sh
mkdir -p out && MAKEFUN_INPUT_DIR=<input> MAKEFUN_OUTPUT_DIR=out node main.ts
```

Node 22, standard library only, no network. Reads `/input/<id>/level.txt`,
writes `/output/<id>/solution.txt` (moves in LURD, one letter per step).
