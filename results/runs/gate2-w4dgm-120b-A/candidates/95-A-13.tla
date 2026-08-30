---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells

vars == <<cells>>

TypeOK ==
  /\ cells \in [1..N \X 1..N -> BOOLEAN]

Init ==
  /\ cells \in [1..N \X 1..N -> BOOLEAN]

AliveNeighbors(r, c) ==
  Cardinality({d \in 1..N \X 1..N :
    /\ d # <<r, c>>
    /\ cells[d]
    /\ d[1] >= r - 1 /\ d[1] <= r + 1
    /\ d[2] >= c - 1 /\ d[2] <= c + 1})

NextGen(r, c) ==
  IF cells[<<r, c>>]
    THEN IF AliveNeighbors(r, c) \in {2, 3} THEN TRUE ELSE FALSE
    ELSE IF AliveNeighbors(r, c) = 3 THEN TRUE ELSE FALSE

Tick ==
  /\ cells' = [p \in 1..N \X 1..N |-> NextGen(p[1], p[2])]

Next ==
  \/ Tick

Spec == Init /\ [][Next]_vars

====