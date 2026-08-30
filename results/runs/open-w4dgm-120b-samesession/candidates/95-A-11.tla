---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

vars == <<grid>>

TypeOK ==
  /\ grid \in [1..N \X 1..N -> BOOLEAN]

Init ==
  /\ \E g \in [1..N \X 1..N -> BOOLEAN] : grid = g

Neighbors(p) == {q \in 1..N \X 1..N :
                    q # p /\ (q[1] - p[1]) \in -1..1 /\ (q[2] - p[2]) \in -1..1}

LiveCount(p) ==
  Cardinality({q \in Neighbors(p) : grid[q]})

Tick ==
  /\ LET newgrid ==
       [p \in 1..N \X 1..N |-> IF grid[p] /\ LiveCount(p) \in {2, 3} THEN TRUE
                             ELSE IF ~grid[p] /\ LiveCount(p) = 3 THEN TRUE
                             ELSE FALSE]
     IN grid' = newgrid

Next == Tick

Spec == Init /\ [][Next]_vars

====