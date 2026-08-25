---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLE cells

(*--------------------------------------------------------------------
  Utility definitions
--------------------------------------------------------------------*)
Pos == 1..N \X 1..N

Offsets == {<<dx, dy>> \in -1..1 \X -1..1 : <<dx, dy>> # <<0,0>>}

Neighbors(p) == 
  LET i == p[1] 
      j == p[2] 
  IN { <<i + dx, j + dy>> \in Pos : <<dx, dy>> \in Offsets }

LiveNeighborCount(p) == 
  Cardinality({ q \in Pos : q \in Neighbors(p) /\ cells[q] })

(*--------------------------------------------------------------------
  Initial state: each cell is arbitrarily true or false
--------------------------------------------------------------------*)
Init == 
  /\ N \in Nat
  /\ cells \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------
  Next-state relation: simultaneous update according to Game of Life rules
--------------------------------------------------------------------*)
Next == 
  LET cnt(p) == LiveNeighborCount(p) IN
    /\ cells' = [p \in Pos |-> 
          IF (cells[p] /\ (cnt(p) = 2 \/ cnt(p) = 3)) \/ (~cells[p] /\ cnt(p) = 3)
          THEN TRUE
          ELSE FALSE]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<cells>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK == 
  /\ N \in Nat
  /\ cells \in [Pos -> BOOLEAN]

=============================================================================