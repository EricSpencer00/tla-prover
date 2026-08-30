---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N

TypeOK ==
    /\ grid \in [Positions \X Positions -> BOOLEAN]

Init ==
    /\ grid = [p \in Positions \X Positions |-> CHOOSE b \in BOOLEAN : TRUE]

\* The eight neighboring positions of a cell, constrained to the grid.
Neighbors(p) == {q \in Positions \X Positions :
                    q # p /\ (q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1)
                              /\ (q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1)}

LiveNeighbors(p) == Cardinality({q \in Neighbors(p) : grid[q]})

NextState(g) ==
    [p \in Positions \X Positions |->
        IF g[p] THEN LiveNeighbors(p) \in {2, 3} ELSE LiveNeighbors(p) = 3]

Tick ==
    /\ grid' = NextState(grid)
    /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====