---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* The cell mapping: 1..N x 1..N grid positions, each Boolean (alive/dead).
VARIABLES grid

vars == <<grid>>

Cells == 1..N

\* Cells outside the grid are treated as dead; this set collects all valid
\* in-bounds positions, so a cell has a neighbor only if that neighbor is in
\* Cells (counting it as 0 otherwise).
Neighbors(p) == {
  q \in Cells \X Cells :
    LET dr == q[1] - p[1] IN
    LET dc == q[2] - p[2] IN
    dr \in -1..1 /\ dc \in -1..1 /\ ~ (dr = 0 /\ dc = 0)
}

AliveNeighbors(p) == Cardinality({q \in Neighbors(p) : grid[q]})

Init ==
  /\ grid \in [Cells \X Cells -> BOOLEAN]

\* Simultaneous update: every cell is recomputed from the same old state.
Tick ==
  /\ grid' = [p \in Cells \X Cells |->
       IF grid[p]
         THEN AliveNeighbors(p) \in {2, 3}
         ELSE AliveNeighbors(p) = 3]

Spec == Init /\ [][Tick]_vars

TypeOK ==
  /\ grid \in [Cells \X Cells -> BOOLEAN]

====