---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

Cells == {"c" \in 1..(N * N) : TRUE}

Rows == 1..N
Cols == 1..N

VARIABLES cells

vars == <<cells>>

Neighbors == {{r, c}, {r, c + 1}, {r, c - 1}, {r - 1, c}, {r + 1, c},
             {r - 1, c - 1}, {r - 1, c + 1}, {r + 1, c - 1}, {r + 1, c + 1}}

InBounds(p) == p[1] \in Rows /\ p[2] \in Cols

LiveNeighbors(p) ==
    Cardinality({q \in Neighbors : InBounds(q) /\ cells[q]})

Init ==
    /\ cells \in [Rows \X Cols -> BOOLEAN]

Tick ==
    /\ cells' = [p \in Rows \X Cols |->
                    LET count == LiveNeighbors(p) IN
                        IF cells[p] /\ (count = 2 \/ count = 3) THEN TRUE
                        ELSE IF ~cells[p] /\ count = 3 THEN TRUE
                        ELSE FALSE]
    /\ UNCHANGED Cells

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == cells \in [Rows \X Cols -> BOOLEAN]

====