---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT N

VARIABLES cells

(*-------------------------------------------------------------------*)
(*   Set of positions on the N×N grid                                 *)
(*-------------------------------------------------------------------*)
Pos == 1..N \X 1..N

(*-------------------------------------------------------------------*)
(*   Neighbourhood of a position (excluding the position itself)     *)
(*-------------------------------------------------------------------*)
Neighbors(p) == { q \in Pos :
                     /\ q # p
                     /\ ABS(q[1] - p[1]) <= 1
                     /\ ABS(q[2] - p[2]) <= 1 }

(*-------------------------------------------------------------------*)
(*   Number of live neighbours of a position                          *)
(*-------------------------------------------------------------------*)
LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : cells[q] })

(*-------------------------------------------------------------------*)
(*   Initial state: any assignment of booleans to the grid cells      *)
(*-------------------------------------------------------------------*)
Init == cells \in [Pos -> BOOLEAN]

(*-------------------------------------------------------------------*)
(*   The deterministic simultaneous update (the "Tick")               *)
(*-------------------------------------------------------------------*)
Next ==
   /\ cells' = [p \in Pos |-> 
        IF (cells[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3))
              \/ (~cells[p] /\ LiveNeighbors(p) = 3)
        THEN TRUE
        ELSE FALSE]

(*-------------------------------------------------------------------*)
(*   Type invariant                                                   *)
(*-------------------------------------------------------------------*)
TypeOK == cells \in [Pos -> BOOLEAN]

(*-------------------------------------------------------------------*)
(*   Specification                                                    *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<cells>>

====