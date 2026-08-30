---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

Cells == {1..N} \X {1..N}

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cells -> BOOLEAN]

CountAlive(p) == Cardinality({q \in Cells : grid[q] = TRUE /\ q # p /\ ManhattanDist(p, q) <= 1})

\* The Game of Life uses the Chebyshev distance (max norm) for neighbor counting,
\* counting all surrounding cells horizontally, vertically, and diagonally.
ManhattanDist(a, b) == IF a = b THEN 0 ELSE IF a[1] = b[1] /\ a[2] = b[2] THEN 1
                        ELSE IF a[1] = b[1] \/ a[2] = b[2] THEN 1 ELSE 2

Init == \E f \in [Cells -> BOOLEAN] : grid = f

Tick == grid' = [p \in Cells |-> IF grid[p] /\ CountAlive(p) \in {2, 3}
                                   THEN TRUE
                                   ELSE IF ~grid[p] /\ CountAlive(p) = 3
                                   THEN TRUE
                                   ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====