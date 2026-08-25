---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE A

(* ---------------------------------------------------------------------- *)
(*   The set of all cell positions on the N-by-N grid                      *)
(* ---------------------------------------------------------------------- *)
Pos == 1..N
Cells == { <<i, j>> : i \in Pos /\ j \in Pos }

(* ---------------------------------------------------------------------- *)
(*   Neighbor definition: cells that are horizontally, vertically or      *)
(*   diagonally adjacent, staying inside the grid boundaries               *)
(* ---------------------------------------------------------------------- *)
NeighborSet(c) ==
  { <<r, col>> :
      r \in Pos /\ col \in Pos /\
      r \in {c[1]-1, c[1], c[1]+1} /\ col \in {c[2]-1, c[2], c[2]+1} /\
      ~(r = c[1] /\ col = c[2]) }

LiveNeighbors(c) ==
  Cardinality({ n \in NeighborSet(c) : A[n] })

(* ---------------------------------------------------------------------- *)
(*   Initial state: every cell may be either alive (TRUE) or dead (FALSE) *)
(* ---------------------------------------------------------------------- *)
Init ==
  A \in [Cells -> BOOLEAN]

(* ---------------------------------------------------------------------- *)
(*   Next-state relation: simultaneous update of all cells                *)
(* ---------------------------------------------------------------------- *)
Next ==
  /\ A' = [c \in Cells |->
          IF (A[c] /\ LiveNeighbors(c) \in {2,3}) \/
             (~A[c] /\ LiveNeighbors(c) = 3)
          THEN TRUE
          ELSE FALSE]

(* ---------------------------------------------------------------------- *)
(*   Type invariant: A always maps each cell to a Boolean value           *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  A \in [Cells -> BOOLEAN]

(* ---------------------------------------------------------------------- *)
(*   Specification: initial condition together with always-enabled Next   *)
(* ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_A

=============================================================================