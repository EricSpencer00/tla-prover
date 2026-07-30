---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Grid == 1 .. N

Positions == [r : Grid, c : Grid]

VARIABLES cells

vars == << cells >>

\* How many of the eight neighboring cells are alive.  Cells outside the
\* NxN grid are treated as dead.
NeighborsAlive(p) ==
  LET neigh == {{-1, -1}, {-1, 0}, {-1, 1}, {0, -1}, {0, 1}, {1, -1}, {1, 0}, {1, 1}}
  IN Cardinality({o \in neigh : cells[[p.r + o[1], p.c + o[2]]] = TRUE})

Init ==
  /\ cells = [p \in Positions |-> CHOOSE b \in BOOLEAN : TRUE]

\* Every cell on the grid updates simultaneously, using the live-neighbor
\* count computed from the current configuration.
Tick ==
  /\ cells' = [p \in Positions |-> IF cells[p] = TRUE
                                 THEN (NeighborsAlive(p) \in {2, 3})
                                 ELSE (NeighborsAlive(p) = 3)]
  /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]

====