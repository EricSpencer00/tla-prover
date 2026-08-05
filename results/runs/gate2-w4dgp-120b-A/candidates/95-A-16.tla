---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells
vars == <<cells>>

Positions == (0..(N - 1)) \X (0..(N - 1))
Deltas == {d \in (-1..1) \X (-1..1) : d # <<0, 0>>}

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]

Init ==
  /\ cells \in [Positions -> BOOLEAN]

LiveNeighbors(p) ==
  Cardinality(
    {q \in Positions :
       /\ q # p
       /\ LET dr == q[1] - p[1]
          dc == q[2] - p[2]
       IN <<dr, dc>> \in Deltas
       /\ cells[q]})


Tick ==
  /\ cells' = [p \in Positions |-> IF cells[p]
                 THEN LiveNeighbors(p) \in {2, 3}
                 ELSE LiveNeighbors(p) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

====