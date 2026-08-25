---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLE grid

(*---------------------------------------------------------------------*)
(*   The set of positions on the N×N grid.  Each position is a pair   *)
(*   ⟨row, column⟩ with both components in 1..N.                       *)
(*---------------------------------------------------------------------*)
Pos == 1..N \X 1..N

(*---------------------------------------------------------------------*)
(*   A cell is alive iff its value in the mapping `grid` is TRUE.      *)
(*---------------------------------------------------------------------*)
Init == 
    /\ grid \in [Pos -> BOOLEAN]

(*---------------------------------------------------------------------*)
(*   Helper definitions for neighbor counting.                         *)
(*---------------------------------------------------------------------*)
NeighborSet(p) == 
    { q \in Pos :
        q # p /\ 
        Abs(q[1] - p[1]) <= 1 /\ 
        Abs(q[2] - p[2]) <= 1 }

LiveNeighbors(p) == 
    Cardinality( { q \in NeighborSet(p) : grid[q] } )

(*---------------------------------------------------------------------*)
(*   The simultaneous update of the whole grid (the "tick").          *)
(*---------------------------------------------------------------------*)
Next == 
    /\ grid' = [ p \in Pos |-> 
          IF grid[p] 
          THEN (LiveNeighbors(p) = 2) \/ (LiveNeighbors(p) = 3) 
          ELSE (LiveNeighbors(p) = 3) ]

Spec == Init /\ [][Next]_<<grid>>

(*---------------------------------------------------------------------*)
(*   Type invariant: `grid` is always a total mapping from positions   *)
(*   to Boolean values.                                                *)
(*---------------------------------------------------------------------*)
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================