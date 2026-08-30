---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A grid position is a row/column pair within the N-by-N square.
Positions == 1..N

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

Init ==
  \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

\* Count live neighbors of a cell, treating positions outside the grid as dead.
LiveNeighbors(p) ==
  Cardinality({q \in Positions \X Positions :
                 q # p /\ q[1] >= 1 /\ q[1] <= N /\ q[2] >= 1 /\ q[2] <= N
                 /\ grid[q]})

\* The entire grid updates simultaneously according to the Game of Life rules.
Tick ==
  /\ \E g \in [Positions \X Positions -> BOOLEAN] :
       \A p \in Positions \X Positions :
         g[p] = IF grid[p] /\ LiveNeighbors(p) \in {2, 3}
                 THEN TRUE
                 ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3
                 THEN TRUE
                 ELSE FALSE
  /\ grid' = g

Next == Tick

Spec == Init /\ [][Next]_vars

====