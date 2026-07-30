---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Cells is the set of positions in the N-by-N grid.
\* A cell outside the grid is treated as dead when counting neighbors.
Cells == (0 .. (N - 1)) \X (0 .. (N - 1))

\* Deltas that reach neighbors: horizontally, vertically, diagonally.
NeighborDeltas == {p \in Cells : p[1] <= 1 /\ p[2] <= 1 /\ p # <<0, 0>>}

RECURSIVE CountAt(_, _, _)
CountAt(g, i, j) ==
  IF i < 0 \/ i >= N \/ j < 0 \/ j >= N THEN 0
  ELSE LET cell == IF g[i, j] = TRUE THEN 1 ELSE 0 IN cell

\* Number of live neighbors of position (i, j) in grid g.
\* Neighbors outside the grid contribute no live cells.
Neighbors(g, i, j) ==
  CountAt(g, i - 1, j - 1) + CountAt(g, i - 1, j) + CountAt(g, i - 1, j + 1)
    + CountAt(g, i, j - 1) + CountAt(g, i, j + 1)
    + CountAt(g, i + 1, j - 1) + CountAt(g, i + 1, j) + CountAt(g, i + 1, j + 1)

VARIABLES cells

vars == <<cells>>

TypeOK == cells \in [Cells -> BOOLEAN]

Init ==
  /\ cells \in [Cells -> BOOLEAN]

\* Tick updates every cell simultaneously according to the Game of Life rule:
\* - a live cell survives with exactly 2 or 3 live neighbors;
\* - a dead cell becomes alive with exactly 3 live neighbors;
\* - otherwise the cell becomes dead.
Tick ==
  /\ cells' = [p \in Cells |->
        LET n == Neighbors(cells, p[1], p[2]) IN
          IF cells[p] THEN (n = 2 \/ n = 3) ELSE (n = 3)]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====