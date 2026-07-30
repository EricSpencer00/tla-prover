---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == {p \in (1..N) \X (1..N)}

Neighbors(p) ==
  {q \in Positions : q # p /\ (q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1) /\ (q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1)}

LiveNeighbors(p) == Cardinality({q \in Neighbors(p) : grid[q]})

Init ==
  /\ grid \in [Positions -> BOOLEAN]

Tick ==
  /\ grid' = [p \in Positions |-> IF grid[p] /\ LiveNeighbors(p) \in {2, 3} THEN TRUE
                                   ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3 THEN TRUE
                                   ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Positions -> BOOLEAN]

====