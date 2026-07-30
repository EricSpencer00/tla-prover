---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

VARIABLES cells

vars == <<cells>>

Positions == {p \in (1..N) \X (1..N)}

\* A cell outside the square grid is considered dead, which is what makes the
\* neighbor count well-defined even at the edges.
Within(p) == p[1] >= 1 /\ p[1] <= N /\ p[2] >= 1 /\ p[2] <= N

Neighbors(p) == {q \in ((p[1] - 1)..(p[1] + 1)) \X ((p[2] - 1)..(p[2] + 1))
                   : q # p}
LiveNeighbors(p) == Cardinality({q \in Neighbors(p) : Within(q) /\ cells[q]})

\* The initial configuration is completely free: every cell is nondeterministically
\* alive or dead, so the entire reachable state space is explored.
Init ==
  /\ cells \in [Positions -> BOOLEAN]

Tick ==
  /\ cells' = [p \in Positions |-> (LiveNeighbors(p) = 2) \/ (LiveNeighbors(p) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]

====