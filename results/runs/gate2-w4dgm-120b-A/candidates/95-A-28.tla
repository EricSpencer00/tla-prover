---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences

CONSTANTS N

\* A position on the N-by-N grid, using row-major numbering.
Positions == 1..N

VARIABLES grid
vars == <<grid>>

\* The count of live neighbors around cell (i, j); off-grid cells are dead.
Neighbors(i, j) ==
  LET deltas == {1, 2, 3} \ {((i + j) % 4) + 1} IN
  Cardinality({d \in deltas : ((i + d - 1) % N) + 1 \in Positions
                                 /\ ((j + d - 1) % N) + 1 \in Positions
                                 /\ grid[((i + d - 1) % N) + 1, ((j + d - 1) % N) + 1]})

Init ==
  \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

\* Every cell updates simultaneously based on its live-neighbor count.
Tick ==
  grid' = [p \in Positions \X Positions |->
             LET n == Neighbors(p[1], p[2]) IN
               IF grid[p] THEN (n = 2) \/ (n = 3) ELSE (n = 3)]

Spec == Init /\ [][Tick]_vars

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

====