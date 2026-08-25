---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLES Grid

(* The set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* Number of live neighbours of a position p *)
LiveNeighbors(p) ==
    Cardinality(
        { q \in Pos :
            q # p /\ 
            Abs(q[1] - p[1]) <= 1 /\ 
            Abs(q[2] - p[2]) <= 1 /\ 
            Grid[q] } )

(* Initial state: any assignment of true/false to each cell *)
Init ==
    Grid \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells *)
Next ==
    \A p \in Pos :
        LET cnt == LiveNeighbors(p) IN
        Grid' [p] =
            IF Grid[p] THEN (cnt = 2 \/ cnt = 3)
            ELSE (cnt = 3)

(* Full specification *)
Spec == Init /\ [][Next]_<<Grid>>

(* Type invariant *)
TypeOK == Grid \in [Pos -> BOOLEAN]

====