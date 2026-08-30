---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A position is a row/column pair within the N-by-N grid.
Positions == 1..N

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

\* Count the number of live (true) neighbors of position p, treating cells
\* outside the grid as dead (value ZERO) by the filter on the domain.
LiveNeighbors(p) ==
  Cardinality({q \in Positions \X Positions :
                 q /= p /\ grid[q]
                 /\ ABS(p[1] - q[1]) <= 1 /\ ABS(p[2] - q[2]) <= 1})

Constrains ==
  \A p \in Positions \X Positions : grid[p] \in BOOLEAN

Init ==
  \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

\* The entire grid updates simultaneously, purely deterministically given the
\* current generation -- no nondeterministic choice occurs here.
Tick ==
  grid' = [p \in Positions \X Positions |->
             IF grid[p] /\ LiveNeighbors(p) \in {2, 3} THEN TRUE
             ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3 THEN TRUE
             ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====