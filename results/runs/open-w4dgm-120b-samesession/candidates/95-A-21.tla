---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 2

Cells == 1..N

VARIABLES grid
vars == <<grid>>

Init == \E g \in [Cells \X Cells -> BOOLEAN] : grid = g

TypeOK == \A p \in Cells \X Cells : grid[p] \in BOOLEAN

NeighborCount(p) ==
  LET deltas == {-1, 0, 1}
      valid(q) == q[1] \in Cells /\ q[2] \in Cells
  IN Cardinality({d \in deltas \X deltas :
        d # <<0, 0>> /\ valid(q = <<p[1] + d[1], p[2] + d[2]>>) /\ grid[<<p[1] + d[1], p[2] + d[2]>>]})

Tick ==
  LET nextState(p) ==
        IF grid[p] = TRUE /\ NeighborCount(p) \in {2,3} THEN TRUE
        ELSE IF grid[p] = FALSE /\ NeighborCount(p) = 3 THEN TRUE
        ELSE FALSE
  IN grid' = [p \in Cells \X Cells |-> nextState(p)]

Spec == Init /\ [][Tick]_vars
====