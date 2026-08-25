---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

VARIABLE A

(*--- Definition of the set of cell positions---*)
Cell == [r \in 1..N, c \in 1..N]

(*--- Helper function for absolute value---*)
Abs(x) == IF x >= 0 THEN x ELSE -x

(*--- Predicate that tells whether two positions are neighbors---*)
IsNeighbor(p, q) ==
    /\ p # q
    /\ Abs(p.r - q.r) <= 1
    /\ Abs(p.c - q.c) <= 1

(*--- Number of live neighbours of a position---*)
NeighborCount(p) ==
    Cardinality({ q \in Cell : IsNeighbor(p, q) /\ A[q] })

(*--- Update rule for a single cell---*)
Update(p) ==
    LET cnt == NeighborCount(p) IN
        (A[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~A[p] /\ cnt = 3)

(*--- Type invariant---*)
TypeOK == A \in [Cell -> BOOLEAN]

(*--- Initial state: any assignment of booleans to cells---*)
Init == A \in [Cell -> BOOLEAN]

(*--- Next-state relation: simultaneous update of all cells---*)
Next == \A p \in Cell :
            A'[p] = Update(p)

(*--- The complete specification---*)
Spec == Init /\ [][Next]_<<A>>

====