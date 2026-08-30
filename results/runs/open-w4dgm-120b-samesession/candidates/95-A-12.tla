---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

VARIABLES alive

vars == << alive >>

TypeOK == alive \in [Positions -> BOOLEAN]

Init == \E f \in [Positions -> BOOLEAN] : alive = f

LiveNeighbors(p) ==
  LET Count(dx, dy) == IF (p[1] + dx) \in Rows /\ (p[2] + dy) \in Cols
                       THEN (IF alive[p[1] + dx, p[2] + dy] THEN 1 ELSE 0)
                       ELSE 0
  IN Count(-1, -1) + Count(-1, 0) + Count(-1, 1)
     + Count(0, -1) + Count(0, 1)
     + Count(1, -1) + Count(1, 0) + Count(1, 1)

NextAlive(p) ==
  IF alive[p]
  THEN LiveNeighbors(p) \in {2, 3}
  ELSE LiveNeighbors(p) = 3

Tick == alive' = [p \in Positions |-> NextAlive(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====