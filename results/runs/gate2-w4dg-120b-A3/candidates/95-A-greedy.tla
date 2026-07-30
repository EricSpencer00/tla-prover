---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == {p \in (1..N) \X (1..N)}

Neighbors(p) ==
  {q \in Positions : q # p /\ ABS(q[1] - p[1]) <= 1 /\ ABS(q[2] - p[2]) <= 1}

TypeOK ==
  /\ grid \in [Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions -> BOOLEAN]

Tick ==
  /\ grid' = [p \in Positions |-> Cardinality({q \in Neighbors(p) : grid[q]}) \in {2, 3}]

Next == Tick

Spec == Init /\ [][Next]_vars

====