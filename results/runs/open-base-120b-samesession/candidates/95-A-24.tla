---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES Grid

(*--- Domain of grid positions ---*)
Pos == 1..N X 1..N

(*--- Absolute value for integers ---*)
Abs(x) == IF x >= 0 THEN x ELSE -x

(*--- Set of live neighbor positions of p ---*)
LiveNeighbors(p) == 
    { q \in Pos :
        q # p /\ 
        Abs(q[1] - p[1]) <= 1 /\ 
        Abs(q[2] - p[2]) <= 1 /\ 
        Grid[q] }

(*--- Number of live neighbors of p ---*)
NeighborCount(p) == Cardinality(LiveNeighbors(p))

(*--- Initial state: any assignment of booleans to cells ---*)
Init == Grid \in [Pos -> BOOLEAN]

(*--- Simultaneous update of the whole grid ---*)
Next == 
    /\ Grid' = [p \in Pos |-> 
                 IF ( Grid[p] /\ (NeighborCount(p) = 2 \/ NeighborCount(p) = 3) )
                    \/ (~Grid[p] /\ NeighborCount(p) = 3)
                 THEN TRUE ELSE FALSE ]

(*--- Specification ---*)
Spec == Init /\ [][Next]_<<Grid>>

(*--- Type invariant ---*)
TypeOK == Grid \in [Pos -> BOOLEAN]

====