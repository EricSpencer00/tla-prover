---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Positions == {p \in (1..N) \X (1..N)}

Neighbors(p) == {q \in Positions : q # p /\ (q[1] - p[1])^2 <= 1 /\ (q[2] - p[2])^2 <= 1}

RECURSIVE LiveCount(_)
LiveCount(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF cells[x] THEN 1 ELSE 0) + LiveCount(S \ {x})

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]

Init ==
  /\ cells \in [Positions -> BOOLEAN]

Tick ==
  /\ cells' = [p \in Positions |-> LET c == LiveCount(Neighbors(p)) IN
                    IF cells[p] THEN (c = 2 \/ c = 3) ELSE (c = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====