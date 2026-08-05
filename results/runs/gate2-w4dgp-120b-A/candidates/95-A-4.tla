---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == CartesianProduct(1..N, 1..N)

VARIABLES aliveAt

vars == <<aliveAt>>

TypeOK ==
  /\ aliveAt \in [Positions -> BOOLEAN]

Init ==
  /\ aliveAt \in [Positions -> BOOLEAN]

\* The grid has fixed boundaries; positions outside the grid are dead for counting.
NeighborCount(p) ==
  LET nb ==
       { q \in Positions :
           q # p /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1 /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1 }
  IN Cardinality({ q \in nb : aliveAt[q] })

NextAlive(p) ==
  LET n == NeighborCount(p)
  IN IF aliveAt[p] THEN (n = 2 \/ n = 3) ELSE (n = 3)

Tick ==
  /\ aliveAt' = [p \in Positions |-> NextAlive(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====