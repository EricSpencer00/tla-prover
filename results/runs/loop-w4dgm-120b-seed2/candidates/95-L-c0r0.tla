---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N

TypeOK ==
    /\ grid \in [Positions \X Positions -> BOOLEAN]

Init ==
    /\ \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

\* Count live neighbors of cell (r, c), treating positions outside the grid as dead.
LiveNeighbors(r, c) ==
    Cardinality({p \in Positions \X Positions :
        /\ p # <<r, c>>
        /\ grid[p] = TRUE
        /\ p[1] >= r - 1 /\ p[1] <= r + 1
        /\ p[2] >= c - 1 /\ p[2] <= c + 1})

\* Simultaneous update: the entire grid is recomputed from the current state.
Tick ==
    /\ grid' = [p \in Positions \X Positions |->
                    LET n == LiveNeighbors(p[1], p[2]) IN
                    IF grid[p] = TRUE THEN n = 2 \/ n = 3
                    ELSE n = 3]
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====