---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

Cells == {"c" \in 1..N \X 1..N}

VARIABLES alive

vars == <<alive>>

Neighbors == (-1)..1

TypeOK ==
    /\ alive \in [Cells -> BOOLEAN]

Init ==
    /\ alive \in [Cells -> BOOLEAN]

LiveNeighbors(c) ==
    LET deltas == {dx \in Neighbors, dy \in Neighbors : ~(dx = 0 /\ dy = 0)} IN
    Cardinality({d \in deltas :
        LET pos == <<c[1] + d[1], c[2] + d[2]>> IN
            /\ pos[1] \in 1..N /\ pos[2] \in 1..N
            /\ alive[pos]})


Tick ==
    /\ alive' = [c \in Cells |-> LET n == LiveNeighbors(c) IN
                    IF alive[c] THEN n = 2 \/ n = 3 ELSE n = 3]
    /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====