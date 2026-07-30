---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* The set of grid coordinates; finite because N is bounded.
Cells == 1..N \X 1..N

\* The value of a cell outside the grid; always dead, used for neighbor counting.
OUTSIDE == FALSE

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
    /\ grid \in [Cells -> BOOLEAN]

\* The number of live neighbors of cell c, counting only actual grid cells
\* and treating any coordinate outside the grid as dead (OUTSIDE).
NbrAlive(c) ==
    LET
        dr == {-1, 0, 1}
        dc == {-1, 0, 1}
        AliveAt(r, col) == IF <<r, col>> \in Cells THEN grid[<<r, col>>] ELSE OUTSIDE
    IN
        Cardinality({<<r, col>> \in Cells :
                        r \in {c[1] + x : x \in dr} /\ col \in {c[2] + y : y \in dc}
                        /\ ~(x = 0 /\ y = 0) /\ AliveAt(r, col)})

\* Simultaneous deterministic update of the entire grid.
Tick ==
    /\ grid' = [c \in Cells |-> LET n == NbrAlive(c) IN IF grid[c] THEN (n = 2 \/ n = 3) ELSE (n = 3)]

\* A live cell with two or three live neighbors survives; a dead cell with
\* exactly three live neighbors is born; everything else dies.
Survival ==
    \A c \in Cells : grid[c] => (NbrAlive(c) = 2 \/ NbrAlive(c) = 3)
Birth ==
    \A c \in Cells : ~grid[c] => (NbrAlive(c) = 3)

Next == Tick

Spec == Init /\ [][Next]_vars

====