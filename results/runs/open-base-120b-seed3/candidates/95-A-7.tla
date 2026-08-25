---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

VARIABLE grid

(*--- Helper definitions ---------------------------------------------------*)
Cell == { <<i, j>> : i \in 1..N, j \in 1..N }

Row(c) == c[1]
Col(c) == c[2]

Abs(x) == IF x >= 0 THEN x ELSE -x

IsNeighbor(c, n) ==
    /\ Abs(Row(c) - Row(n)) <= 1
    /\ Abs(Col(c) - Col(n)) <= 1
    /\ c # n

LiveNeighbors(c) ==
    Cardinality({ n \in Cell : IsNeighbor(c, n) /\ grid[n] })

(*--- Initialization -------------------------------------------------------*)
Init ==
    grid \in [Cell -> BOOLEAN]

(*--- Transition relation ---------------------------------------------------*)
Next ==
    \E grid' \in [Cell -> BOOLEAN] :
        /\ \A c \in Cell :
            grid'[c] =
                (grid[c] /\ (LiveNeighbors(c) = 2 \/ LiveNeighbors(c) = 3))
                \/ (~grid[c] /\ LiveNeighbors(c) = 3)

(*--- Specification --------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<grid>>

(*--- Type invariant -------------------------------------------------------*)
TypeOK ==
    grid \in [Cell -> BOOLEAN]

====