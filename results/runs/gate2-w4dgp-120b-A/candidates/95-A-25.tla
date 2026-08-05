---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Each cell is identified by its row/column position; Grid is the set of positions.
Positions == 1..N
Cells == Positions \X Positions

\* Neighbors(p) is the set of positions adjacent (including diagonals) to position p
\* that lie inside the grid; positions outside the grid are not included, which is
\* equivalent to treating off-grid cells as permanently dead (value 0) when counting.
Neighbors(p) == { q \in Cells : q # p /\ Cardinality({d \in {0, 1} : \E r \in Positions : q = <<p[1] + d, p[2] + (r - p[2])>> })
                        + Cardinality({d \in {0, 1} : \E c \in Positions : q = <<p[1] + (d - p[1]), p[2] + d>> })
                        + Cardinality({d \in {0, 1} : q = <<p[1] + (d - p[1]), p[2] + (d - p[2])>> }) >= 1 }

\* Sum of live neighbors for a position; each neighbor contributes 1 if alive, 0 otherwise.
LiveSum(g) == [p \in Cells |-> Cardinality({ q \in Neighbors(p) : g[q] })]

VARIABLES grid

TypeOK == grid \in [Cells -> BOOLEAN]

Init == \E g \in [Cells -> BOOLEAN] : grid = g

\* Simultaneous update: the next state at every position is computed from the
\* current state's live-sum, so one generation fully determines the next.
Tick ==
    /\ \E g2 \in [Cells -> BOOLEAN] : g2 = [p \in Cells |->
                        IF grid[p] /\ (LiveSum(grid)[p] = 2 \/ LiveSum(grid)[p] = 3)
                        THEN TRUE
                        ELSE IF ~grid[p] /\ LiveSum(grid)[p] = 3
                        THEN TRUE
                        ELSE FALSE]
    /\ grid' = g2

Next == Tick

Spec == Init /\ [][Next]_grid

====