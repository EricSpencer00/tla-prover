---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Blank == "Blank"

VARIABLES cell

vars == <<cell>>

Positions == {p \in (0..(N - 1)) \X (0..(N - 1)) : TRUE}

Neighbors(p) ==
  {q \in Positions :
     (q # p) /\ (q[1] >= p[1] - 1) /\ (q[1] <= p[1] + 1)
       /\ (q[2] >= p[2] - 1) /\ (q[2] <= p[2] + 1)}

LiveCount(p) ==
  Cardinality({q \in Neighbors(p) : cell[q]})

TypeOK == /\ cell \in [Positions -> BOOLEAN]

Init ==
  /\ cell = [p \in Positions |-> CHOOSE b \in BOOLEAN : TRUE]

Generation(c) ==
  [p \in Positions |->
     IF cell[p]
       THEN (LiveCount(p) = 2) \/ (LiveCount(p) = 3)
       ELSE LiveCount(p) = 3]

Next == cell' = Generation(cell)

Spec == Init /\ [][Next]_vars

====