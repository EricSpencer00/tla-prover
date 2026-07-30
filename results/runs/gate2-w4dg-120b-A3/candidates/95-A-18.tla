---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Points == {p \in (1..N) \X (1..N)}

Neighbors(p) ==
  { q \in Points :
      q # p
      /\ NatAbs(p[1] - q[1]) <= 1
      /\ NatAbs(p[2] - q[2]) <= 1 }

LiveNeighbors(p) ==
  Cardinality({ q \in Neighbors(p) : grid[q] })

TypeOK ==
  /\ grid \in [Points -> BOOLEAN]

Init ==
  /\ grid \in [Points -> BOOLEAN]

Step ==
  /\ grid' = [p \in Points |->
        LET n == LiveNeighbors(p) IN
          IF grid[p] THEN n = 2 \/ n = 3 ELSE n = 3]

Next == Step

Spec == Init /\ [][Next]_vars

====