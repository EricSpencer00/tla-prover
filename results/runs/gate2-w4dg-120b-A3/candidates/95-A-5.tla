---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Positions == {p \in (1..N) \X (1..N) : TRUE}

Neighbors(p) == {q \in Positions : q # p /\ Cardinality({d \in {-1, 0, 1} : (p[1] + d) \in 1..N /\ (p[2] + d) \in 1..N /\ q = <<p[1] + d, p[2] + d>>}) >= 1}

Init ==
  /\ cells \in [Positions -> BOOLEAN]

LiveNeighbors(p) ==
  Cardinality({q \in Neighbors(p) : cells[q]})

Tick ==
  /\ cells' = [p \in Positions |->
        LET c == LiveNeighbors(p) IN
          IF cells[p] /\ (c = 2 \/ c = 3) THEN TRUE
          ELSE IF ~cells[p] /\ c = 3 THEN TRUE
          ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == cells \in [Positions -> BOOLEAN]

====