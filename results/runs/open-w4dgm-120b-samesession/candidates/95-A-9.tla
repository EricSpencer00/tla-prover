---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

VARIABLES grid

vars == <<grid>>

Positions == {1 .. N}
Cells == Positions \X Positions
Neighbors == {-1, 0, 1}

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
  /\ \E g \in [Cells -> BOOLEAN] : grid = g
  /\ UNCHANGED <<>>

CountAlive(c) ==
  LET nbrs == { <<c[1] + dx, c[2] + dy>> : dx \in Neighbors, dy \in Neighbors, (dx, dy) # <<0, 0>> }
  IN Cardinality({ n \in nbrs : n \in Cells /\ grid[n] })

Tick ==
  /\ \E g \in [Cells -> BOOLEAN] :
       g = [c \in Cells |-> IF grid[c] /\ CountAlive(c) \in {2, 3} THEN TRUE
                            ELSE IF ~grid[c] /\ CountAlive(c) = 3 THEN TRUE
                            ELSE FALSE]
  /\ grid' = g
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====