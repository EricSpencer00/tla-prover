---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == (1..N) \X (1..N)

\* Each position maps to TRUE (alive) or FALSE (dead); the entire grid updates
\* simultaneously, so the neighbor counts below are all taken from the current
\* generation.  A live cell with 2 or 3 live neighbors survives; a dead cell with
\* exactly 3 live neighbors becomes alive; all others die.

VARIABLES grid

TypeOK == grid \in [Cells -> BOOLEAN]

Init == grid \in [Cells -> BOOLEAN]

NeighborCount(c) ==
    LET deltas == {{-1, -1}, {-1, 0}, {-1, 1}, {0, -1}, {0, 1}, {1, -1}, {1, 0}, {1, 1}} IN
    Cardinality({d \in deltas :
        LET nb == <<c[1] + d[1], c[2] + d[2]>> IN
        IF nb \in Cells /\ grid[nb] THEN d ELSE "none"})

NextState(c) == (grid[c] /\ NeighborCount(c) \in {2, 3}) \/ (~grid[c] /\ NeighborCount(c) = 3)

Tick == grid' = [c \in Cells |-> NextState(c)]

Next == Tick

Spec == Init /\ [][Next]_grid

TypeOKInv == TypeOK

====