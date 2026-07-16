----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The constant N is required to be a natural number (including 0). *)
ASSUME N \in Nat

vars == <<grid>>

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                      *)
(* ------------------------------------------------------------------------- *)

(* Positions on the board: all pairs (x, y) where x and y are between 1 and N. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: every position maps to a Boolean value (TRUE = alive,
   FALSE = dead). *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* Sum: a recursive function that computes the sum of applying a function f   *)
(*      to all elements of a finite set S.                                   *)
(* ------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------------- *)
(* sc: contribution of a single cell to the score of a neighbour.            *)
(*     The contribution is 1 if the cell is alive and inside the board,    *)
(*     otherwise 0.                                                          *)
(* ------------------------------------------------------------------------- *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N
         \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* ------------------------------------------------------------------------- *)
(* score(p): number of alive neighbours of position p.                       *)
(* ------------------------------------------------------------------------- *)
score(p) ==
  LET nbrs  == {<<x, y>> : x, y \in {-1, 0, 1} /\ <<x, y>> # <<0, 0>>}
      points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
  IN Sum(sc, points)

(* ------------------------------------------------------------------------- *)
(* Init: every board cell is assigned a Boolean value.                        *)
(* ------------------------------------------------------------------------- *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* Next: standard Game of Life update rule.                                   *)
(* ------------------------------------------------------------------------- *)
Next ==
  grid' = [p \in Pos |-> IF (grid[p] /\ score(p) \in {2, 3}) \/
                         (~grid[p] /\ score(p) = 3)
                     THEN TRUE
                     ELSE FALSE]

(* ------------------------------------------------------------------------- *)
(* Full specification.                                                       *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

=============================================================================