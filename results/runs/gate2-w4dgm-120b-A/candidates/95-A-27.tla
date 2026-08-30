---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == {1 .. N}

TypeOK ==
  /\ grid \in [Cells \X Cells -> BOOLEAN]

Init ==
  /\ \E g \in [Cells \X Cells -> BOOLEAN] : grid = g

\* A cell outside the grid is treated as dead (zero) when counting neighbors.
NeighborAlive(x, y) ==
  IF x \in Cells /\ y \in Cells
  THEN IF grid[x, y] THEN 1 ELSE 0
  ELSE 0

CountLiveNeighbors(i, j) ==
  NeighborAlive(i - 1, j - 1) + NeighborAlive(i - 1, j) + NeighborAlive(i - 1, j + 1)
  + NeighborAlive(i, j - 1)                         + NeighborAlive(i, j + 1)
  + NeighborAlive(i + 1, j - 1) + NeighborAlive(i + 1, j) + NeighborAlive(i + 1, j + 1)

AliveNext(i, j) ==
  LET n == CountLiveNeighbors(i, j) IN
    IF grid[i, j]
    THEN n = 2 \/ n = 3
    ELSE n = 3

Tick ==
  /\ \E g \in [Cells \X Cells -> BOOLEAN] :
       /\ \A i \in Cells, j \in Cells : g[i, j] = AliveNext(i, j)
       /\ grid' = g
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====