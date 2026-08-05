---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

VALID == {r \in 1..N, c \in 1..N}

TypeOK == grid \in [VALID -> BOOLEAN]

Init ==
    /\ grid \in [VALID -> BOOLEAN]

Neighbors(r, c) ==
    {
        <<r + dr, c + dc>> :
            dr \in -1..1 /\ dc \in -1..1 /\ (dr # 0 \/ dc # 0)
            /\ r + dr \in 1..N /\ c + dc \in 1..N
    }

AliveCount(r, c) ==
    Cardinality({p \in Neighbors(r, c) : grid[p]})

Tick ==
    /\ grid' = [p \in VALID |-> LET a == AliveCount(p[1], p[2]) IN
                    IF grid[p] /\ (a = 2 \/ a = 3) THEN TRUE
                    ELSE IF ~grid[p] /\ a = 3 THEN TRUE ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====