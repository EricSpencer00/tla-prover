---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == (1..N) \X (1..N)

\* Neighbors are the eight positions directly adjacent vertically, horizontally,
\* or diagonally; positions outside the grid count as zero live cells.
Neighbors(p) ==
    {q \in Cells : q \in {(p[1] - 1, p[2] - 1), (p[1] - 1, p[2]), (p[1] - 1, p[2] + 1),
                           (p[1],     p[2] - 1),                 (p[1],     p[2] + 1),
                           (p[1] + 1, p[2] - 1), (p[1] + 1, p[2]), (p[1] + 1, p[2] + 1)}}

\* grid is the full state: which cells are alive. The automaton is deterministic
\* once an initial grid configuration is chosen; each generation follows from it.
VARIABLES grid

vars == <<grid>>

Init ==
    /\ grid \in [Cells -> BOOLEAN]

\* Count live neighbors of position p in the current grid.
LiveNeighbors(p) ==
    Cardinality({q \in Neighbors(p) : grid[q]})

\* The game updates the whole grid at once from the current live-neighbor counts.
Tick ==
    /\ \E newgrid \in [Cells -> BOOLEAN] :
         \A p \in Cells :
            /\ IF grid[p] THEN newgrid[p] = (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
               ELSE newgrid[p] = (LiveNeighbors(p) = 3)
            /\ (newgrid[p] => grid[p] \/ LiveNeighbors(p) = 3)
    /\ grid' = newgrid

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Cells -> BOOLEAN]

====