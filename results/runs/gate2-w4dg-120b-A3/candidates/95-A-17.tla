---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Rows == 0..(N - 1)
Cols == 0..(N - 1)
Positions == Rows \X Cols

VARIABLES status
vars == << status >>

\* value of a cell position; maps positions outside the grid to dead (0)
Value(p) == IF p \in Positions THEN IF status[p] THEN 1 ELSE 0 ELSE 0

AllEight(p) ==
  << p[1] - 1, p[2] - 1 >> \cup
  << p[1] - 1, p[2]     >> \cup
  << p[1] - 1, p[2] + 1 >> \cup
  << p[1],     p[2] - 1 >> \cup
  << p[1],     p[2] + 1 >> \cup
  << p[1] + 1, p[2] - 1 >> \cup
  << p[1] + 1, p[2]     >> \cup
  << p[1] + 1, p[2] + 1 >>

NeighborTotal(p) == Value(AllEight(p)[1]) + Value(AllEight(p)[2]) +
                    Value(AllEight(p)[3]) + Value(AllEight(p)[4]) +
                    Value(AllEight(p)[5]) + Value(AllEight(p)[6]) +
                    Value(AllEight(p)[7]) + Value(AllEight(p)[8])

\* A live cell with 2 or 3 live neighbors survives; a dead cell with exactly
\* 3 live neighbors becomes alive; every other cell goes dead.
NextStatus(p) ==
  IF status[p] THEN (NeighborTotal(p) \in {2, 3}) ELSE (NeighborTotal(p) = 3)

TypeOK == status \in [Positions -> BOOLEAN]

Init ==
  /\ status \in [Positions -> BOOLEAN]

Next ==
  /\ status' = [p \in Positions |-> NextStatus(p)]

Spec == Init /\ [][Next]_vars

====