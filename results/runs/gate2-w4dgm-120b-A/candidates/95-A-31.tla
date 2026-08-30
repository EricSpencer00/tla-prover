---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == 1..N

VARIABLES grid
vars == <<grid>>

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

Init == grid \in [Positions \X Positions -> BOOLEAN]

RECURSIVE CountAlive(_)
CountAlive(S) ==
  IF S = {} THEN 0
  ELSE LET p == CHOOSE x \in S : TRUE IN (IF grid[p] THEN 1 ELSE 0) + CountAlive(S \ {p})

Neighbors(p) == {q \in Positions \X Positions :
                    q # p /\ Cardinality({i \in 1..2 : q[i] = p[i]}) >= 1 /\ ABS(q[1] - p[1]) <= 1 /\ ABS(q[2] - p[2]) <= 1}

NextState(p) == IF grid[p] /\ (CountAlive(Neighbors(p)) \in {2, 3}) \/ (~grid[p] /\ CountAlive(Neighbors(p)) = 3) THEN TRUE ELSE FALSE

Tick == grid' = [p \in Positions \X Positions |-> NextState(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====