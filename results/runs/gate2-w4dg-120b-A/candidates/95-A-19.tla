---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N

\* A cell is addressed by its row and column; both range from 1 to N.
Cells == 1..N \X 1..N

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
    \E g \in [Cells -> BOOLEAN] : grid = g

Within == (x \in Cells) => TRUE

\* For a cell inside the grid, its neighbors are the cells immediately
\* adjacent horizontally, vertically, and diagonally; cells outside the
\* grid are treated as dead (value FALSE) for the purpose of counting.
Neighbors(p) ==
    { q \in Cells : Within(q) /\ p # q /\ Cardinality({ x \in Nat : x \in {p[1] - q[1], p[2] - q[2]} /\ x <= 1 }) }

AliveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

\* Simultaneous update: the new value of each cell depends only on the
\* current grid, so the whole grid advances in one deterministic step.
Tick ==
    /\ \E newgrid \in [Cells -> BOOLEAN] :
        \A p \in Cells :
            LET live == AliveNeighbors(p) IN
                newgrid[p] = IF grid[p] /\ (live = 2 \/ live = 3) THEN TRUE
                               ELSE IF ~grid[p] /\ live = 3 THEN TRUE
                               ELSE FALSE
    /\ grid' = newgrid

Next == Tick

Spec == Init /\ [][Next]_vars

====