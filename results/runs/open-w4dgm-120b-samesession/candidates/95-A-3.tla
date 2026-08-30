---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == (1..N) \X (1..N)

Neighs(c) ==
    {d \in Cells :
        d # c /\ (d[1] >= c[1] - 1 /\ d[1] <= c[1] + 1)
                 /\ (d[2] >= c[2] - 1 /\ d[2] <= c[2] + 1)}

TypeOK == grid \in [Cells -> BOOLEAN]

CountAlive(c) == Cardinality({d \in Neighs(c) : grid[d]})

Init ==
    /\ grid \in [Cells -> BOOLEAN]

Tick ==
    /\ grid' = [c \in Cells |-> IF grid[c]
                   THEN CountAlive(c) \in {2, 3}
                   ELSE CountAlive(c) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

====