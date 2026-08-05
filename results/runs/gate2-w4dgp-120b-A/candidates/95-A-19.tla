---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Positions == 0 .. (N - 1)
NeighborsOf(r, c) ==
  {<<rr, cc>> \in [Positions \X Positions] :
     rr # r \/ cc # c /\ (rr >= r - 1 /\ rr <= r + 1) /\ (cc >= c - 1 /\ cc <= c + 1)}

NumAlive(p, q) == IF cells[p] THEN 1 ELSE 0

TypeOK ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Tick ==
  /\ cells' = {p \in Positions \X Positions :
       LET count == NumAlive(p[1] - 1, p[2] - 1) + NumAlive(p[1] - 1, p[2]) + NumAlive(p[1] - 1, p[2] + 1)
                    + NumAlive(p[1], p[2] - 1)                         + NumAlive(p[1], p[2] + 1)
                    + NumAlive(p[1] + 1, p[2] - 1) + NumAlive(p[1] + 1, p[2]) + NumAlive(p[1] + 1, p[2] + 1)
       IN IF cells[p]
            THEN count = 2 \/ count = 3
            ELSE count = 3}
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====