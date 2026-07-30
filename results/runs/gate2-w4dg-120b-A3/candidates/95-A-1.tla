---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N

Nbrs(p) ==
  Cardinality({q \in Positions \X Positions :
                 q # p
                 /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1
                 /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1
                 /\ grid[q] = TRUE})

Init ==
  /\ grid \in [Positions \X Positions -> BOOLEAN]

Step ==
  /\ grid' = [p \in Positions \X Positions |-> Nbrs(p) = 2 \/ Nbrs(p) = 3]

Next == Step

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

====