---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE A

Cell == 1..N X 1..N

IsNeighbor(p, q) ==
    /\ p # q
    /\ (p[1] - q[1]) \in {-1, 0, 1}
    /\ (p[2] - q[2]) \in {-1, 0, 1}

LiveNeighbors(c) ==
    Cardinality({c2 \in Cell : IsNeighbor(c, c2) /\ A[c2]})

Next ==
    \E newA \in [Cell -> BOOLEAN] :
        /\ \A c \in Cell :
               newA[c] =
                 IF A[c]
                 THEN (LiveNeighbors(c) = 2) \/ (LiveNeighbors(c) = 3)
                 ELSE LiveNeighbors(c) = 3
        /\ A' = newA

Init ==
    A \in [Cell -> BOOLEAN]

Spec == Init /\ [][Next]_A

TypeOK == A \in [Cell -> BOOLEAN]

====