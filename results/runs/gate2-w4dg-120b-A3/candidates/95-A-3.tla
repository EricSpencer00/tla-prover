---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Cells == 1..N

Positions == Cells \X Cells

VARIABLES alive

vars == <<alive>>

\* Off-grid locations are treated as dead, so neighbor counts outside the
\* grid are zero by definition.
Neighbors(p) ==
  { q \in Positions :
      q[1] \in {p[1] - 1, p[1], p[1] + 1} /\ q[2] \in {p[2] - 1, p[2], p[2] + 1}
        /\ q # p }

LiveNeighborCount(p) ==
  Cardinality({ q \in Neighbors(p) : alive[q] })

Init ==
  \E f \in [Positions -> BOOLEAN] : alive = f

Next ==
  \E g \in [Positions -> BOOLEAN] :
    /\ \A p \in Positions :
         IF alive[p] THEN
           g[p] <=> (LiveNeighborCount(p) = 2 \/ LiveNeighborCount(p) = 3)
         ELSE
           g[p] <=> (LiveNeighborCount(p) = 3)
    /\ alive' = g

Spec == Init /\ [][Next]_vars

TypeOK == alive \in [Positions -> BOOLEAN]

====