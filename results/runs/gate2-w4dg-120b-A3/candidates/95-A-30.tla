---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == [1..N, 1..N]

Neighbors == {
    <<dx, dy>> \in [1..N, 1..N, 1..N, 1..N] :
        (dx # 0 \/ dy # 0) /\ dx >= -1 /\ dx <= 1 /\ dy >= -1 /\ dy <= 1
}

\* A neighbor counted off the grid is simply ignored and contributes nothing.
CountLive(r, c) ==
    Cardinality({
        <<r + dx, c + dy>> \in Cells :
            grid[r + dx, c + dy]
    })

Init ==
    /\ grid \in [Cells -> BOOLEAN]

Tick ==
    /\ grid' = [p \in Cells |-> IF
                    LET live == CountLive(p[1], p[2]) IN
                        IF grid[p] THEN live = 2 \/ live = 3 ELSE live = 3
                ]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Cells -> BOOLEAN]
====