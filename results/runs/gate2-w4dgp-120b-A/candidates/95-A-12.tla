---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Row == 1..N
Col == 1..N
Pos == Row \X Col
NeighborOffsets == {p \in Row \X Col : p[1] \in {0, 1, 2} /\ p[2] \in {0, 1, 2} /\ p # <<0, 0>>}

\* A cell outside the N-by-N grid is treated as dead for neighbor counting.
OutsideGrid(p) == p[1] < 1 \/ p[1] > N \/ p[2] < 1 \/ p[2] > N

LiveNeighbors(c) ==
    LET f(T, Acc) ==
        IF T = {} THEN Acc
        ELSE LET y == CHOOSE z \in T : TRUE IN
             IF OutsideGrid(c + y) THEN f(T \ {y}, Acc)
             ELSE IF cells[c + y] THEN f(T \ {y}, Acc + 1) ELSE f(T \ {y}, Acc)
    IN f(NeighborOffsets, 0)

TypeOK ==
    /\ cells \in [Pos -> BOOLEAN]

Init ==
    /\ cells \in [Pos -> BOOLEAN]

Tick ==
    /\ cells' = [c \in Pos |-> IF cells[c] /\ (LiveNeighbors(c) = 2 \/ LiveNeighbors(c) = 3)
                          THEN TRUE
                          ELSE IF ~cells[c] /\ LiveNeighbors(c) = 3
                          THEN TRUE
                          ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====