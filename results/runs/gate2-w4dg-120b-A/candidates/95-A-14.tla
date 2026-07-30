---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

TypeOK ==
    /\ grid \in [1..N \X 1..N -> BOOLEAN]

Neighbors(p) ==
    LET [i, j] == p IN
    {
        <<i + di, j + dj>> :
            di \in { -1, 0, 1 } /\ dj \in { -1, 0, 1 } /\ ~(di = 0 /\ dj = 0)
                /\ i + di \in 1..N /\ j + dj \in 1..N
    }

LiveCount(p) ==
    Cardinality({ c \in Neighbors(p) : grid[c] })

Init ==
    /\ grid \in [1..N \X 1..N -> BOOLEAN]

LiveNeighbors(p) == LiveCount(p)

Tick ==
    /\ grid' = [p \in 1..N \X 1..N |->
                    IF grid[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
                        THEN TRUE
                        ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3
                            THEN TRUE
                            ELSE FALSE]
    /\ UNCHANGED << >>

Spec ==
    /\ Init
    /\ [][Tick]_vars

====