---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Positions == (1..N) \X (1..N)

\* A cell outside the grid is treated as dead (0 live neighbors from it).
InGrid == {p \in Positions : TRUE}

VARIABLES grid

vars == <<grid>>

TypeOK == /\ grid \in [Positions -> BOOLEAN]

Init0(b) == {p \in Positions : b[p]}
Init1 == Init0([p \in Positions |-> IF p = CHOOSE q \in Positions : TRUE THEN TRUE ELSE FALSE])

Init == \/ \E b \in BOOLEAN^{Positions} : grid = b

\* Neighborhood count works for in-grid cells and treats out-of-grid cells as dead.
LiveNeighbors(p) ==
  Cardinality({q \in Positions :
                 /\ q # p
                 /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1
                 /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1
                 /\ grid[q]})

Next == \/ \E p \in Positions :
            /\ (grid[p] /\ LiveNeighbors(p) \in {2, 3}) \/ (~grid[p] /\ LiveNeighbors(p) = 3)
            /\ grid' = [grid EXCEPT ![p] = (grid[p] /\ LiveNeighbors(p) \in {2, 3})
                                                \/ (~grid[p] /\ LiveNeighbors(p) = 3)]

Next == \E p \in Positions : Next

Spec == Init /\ [][Next]_vars

====