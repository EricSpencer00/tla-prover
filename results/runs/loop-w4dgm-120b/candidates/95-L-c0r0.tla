---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N

Neighbors(p) ==
    { q \in Positions \X Positions :
        q # p /\ \A i \in 1..2 : q[i] \in Positions /\ q[i] >= p[i] - 1 /\ q[i] <= p[i] + 1 }

Init ==
    /\ grid \in [Positions \X Positions -> BOOLEAN]

LiveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

NextGrid ==
    [ p \in Positions \X Positions |->
        IF grid[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
        THEN TRUE
        ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3
        THEN TRUE
        ELSE FALSE ]

Tick ==
    /\ grid' = NextGrid

Next ==
    \/ Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ grid \in [Positions \X Positions -> BOOLEAN]

====