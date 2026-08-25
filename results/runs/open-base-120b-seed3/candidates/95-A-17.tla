---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N
VARIABLE A

(*--------------------------------------------------------------------*)
(* The set of positions on the N-by-N grid *)
Pos == 1..N \X 1..N

(*--------------------------------------------------------------------*)
(* Helper predicate: p and q are distinct neighboring cells *)
IsNeighbor(p, q) ==
    /\ p # q
    /\ (p[1] - q[1]) \in -1..1
    /\ (p[2] - q[2]) \in -1..1

(*--------------------------------------------------------------------*)
(* Number of live neighbors of a cell p in the current state *)
NeighborCount(p) ==
    Cardinality({ q \in Pos : IsNeighbor(p, q) /\ A[q] })

(*--------------------------------------------------------------------*)
(* Type invariant *)
TypeOK == A \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------*)
(* Initial state: any assignment of booleans to the grid cells *)
Init == A \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------*)
(* One simulation step (simultaneous update) *)
Next ==
    /\ A' = [p \in Pos |-> 
            IF ( A[p] /\ (NeighborCount(p) = 2 \/ NeighborCount(p) = 3) )
                \/ ( ~A[p] /\ NeighborCount(p) = 3 )
            THEN TRUE
            ELSE FALSE ]

(*--------------------------------------------------------------------*)
(* Overall specification *)
Spec == Init /\ [][Next]_<<A>>

=============================================================================