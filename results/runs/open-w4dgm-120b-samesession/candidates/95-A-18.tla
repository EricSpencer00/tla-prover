---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A Conway's Game of Life grid: each cell is alive (TRUE) or dead (FALSE), and the
\* entire grid updates simultaneously each step based on neighbor counts. The grid is
\* fixed-size with dead boundaries (outside cells are zero).
Cells == 1 .. N

VARIABLES grid
vars == <<grid>>

TypeOK == grid \in [Cells \X Cells -> BOOLEAN]

Init ==
  \E g \in [Cells \X Cells -> BOOLEAN] : grid = g

\* Helper: the set of grid positions a given position is adjacent to (including
\* diagonals), clipped to the grid so there are no out-of-bounds positions to wrap.
Neighbors(p) == { q \in Cells \X Cells :
                    q # p /\ \E dr \in -1 .. 1, dc \in -1 .. 1 :
                      dr^2 + dc^2 >= 1 /\ p[1] + dr = q[1] /\ p[2] + dc = q[2] }

LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

\* Tick: every cell on the grid updates simultaneously, according to the classic
\* Game of Life rules applied to the current neighbor count.
Tick ==
  \E newGrid \in [Cells \X Cells -> BOOLEAN] :
    /\ newGrid = [p \in Cells \X Cells |->
                    IF grid[p] /\ LiveNeighbors(p) \in {2, 3} THEN TRUE
                    ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3 THEN TRUE
                    ELSE FALSE]
    /\ grid' = newGrid

Next == Tick

Spec == Init /\ [][Next]_vars

\* Each cell's value stays a Boolean, and every grid position always has a value,
\* so no cell is ever silently dropped or left in an indeterminate state.
TypeOKInv == TypeOK
====