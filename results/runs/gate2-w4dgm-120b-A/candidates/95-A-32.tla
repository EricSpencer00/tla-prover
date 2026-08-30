---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N
Neighbors == {p \in Positions \X Positions : p # <<0, 0>>}
Outside(p) == IF p[1] < 1 \/ p[1] > N \/ p[2] < 1 \/ p[2] > N THEN TRUE ELSE FALSE

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

Init == \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

LiveCount(p) ==
  LET nbrs == {q \in Positions \X Positions : q # p /\ \A d \in {-1, 0, 1} \X {-1, 0, 1} \ {<<0, 0>>} : q = <<p[1] + d[1], p[2] + d[2]>>}
      inside == {q \in nbrs : ~Outside(q)}
  IN Cardinality({q \in inside : grid[q]})

Tick ==
  /\ grid' = [p \in Positions \X Positions |->
                IF grid[p] /\ LiveCount(p) \in {2, 3} THEN TRUE
                ELSE IF ~grid[p] /\ LiveCount(p) = 3 THEN TRUE
                ELSE FALSE]
  /\ UNCHANGED <<>>

Spec == Init /\ [][Tick]_vars

TypeOKInv == TypeOK
====