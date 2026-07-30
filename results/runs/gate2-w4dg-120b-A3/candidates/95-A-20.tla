---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

Positions == 1..N \X 1..N

VARIABLES grid
vars == <<grid>>

NeighborOffsets == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>, <<0, -1>>, <<0, 1>>, <<1, -1>>, <<1, 0>>, <<1, 1>>}

Neighbors(p) == {q \in Positions : q[1] = p[1] + d[1] /\ q[2] = p[2] + d[2] /\ d \in NeighborOffsets}

LiveCount(p) == Cardinality({q \in Neighbors(p) : grid[q]})

TypeOK ==
  /\ grid \in [Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions -> BOOLEAN]

Tick ==
  /\ grid' = [p \in Positions |-> IF LiveCount(p) \in {2, 3} THEN grid[p] ELSE (LiveCount(p) = 3)]
  /\ UNCHANGED vars

Next == Tick

Spec == Init /\ [][Next]_vars

====