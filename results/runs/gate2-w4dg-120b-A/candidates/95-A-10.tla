---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANTS N

Cells == 1 .. N

Positions == [row : Cells, col : Cells]

Neighbors(p) ==
  { q \in Positions :
      q # p /\ ABS(q.row - p.row) <= 1 /\ ABS(q.col - p.col) <= 1 }

VARIABLES alive

TypeOK ==
  /\ alive \in [Positions -> BOOLEAN]

Init ==
  /\ alive \in [Positions -> BOOLEAN]

LiveCount(p) ==
  Cardinality({ q \in Positions : q # p /\ alive[q] })

Next ==
  /\ alive' = [p \in Positions |->
                 LET c == LiveCount(p) IN
                   IF alive[p] THEN c \in {2, 3} ELSE c = 3]
  /\ UNCHANGED <<>>

Spec == Init /\ [][Next]_<<alive>>

====