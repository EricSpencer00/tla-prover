----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N

VARIABLE grid

(* The constant N is assumed to be a natural number. *)
ASSUME N \in Nat

(* A convenient alias for the set of all variables. *)
vars == grid

(* ------------------------------------------------------------------------- *)
(* Recursive summation of a function f over a finite set S.                  *)
(* ------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* The set of all positions on the NxN board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------------- *)
(* TypeOK is true exactly when grid maps every position to a Boolean value.  *)
(* The original specification used "\notin", which made the invariant        *)
(* false for every concrete state.  Here we correct the predicate to        *)
(* reflect the intended type constraint.                                     *)
(* ------------------------------------------------------------------------- *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* Score contribution of a single cell:                                       *)
(*   - If the cell (or any of its 8 neighbours) lies outside the board,      *)
(*     it contributes 0.                                                       *)
(*   - Otherwise it contributes 1.                                            *)
(* ------------------------------------------------------------------------- *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE
    \/ x = 0 \/ y = 0
    \/ x > N \/ y > N
    \/ ~grid[<<x, y>>] -> 0
    [] TRUE -> 1

(* ------------------------------------------------------------------------- *)
(* The total score for a position p is the sum of the contributions of its   *)
(* eight neighbours (the cell itself is excluded).                           *)
(* ------------------------------------------------------------------------- *)
score(p) ==
  LET nbrs  == {x \in {-1, 0, 1} \X {-1, 0, 1} : x # <<0, 0>>}
      points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
  IN Sum(sc, points)

(* ------------------------------------------------------------------------- *)
(* Initial state: any mapping from the board positions to Boolean values.    *)
(* ------------------------------------------------------------------------- *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* Transition relation: standard Game of Life update rule.                   *)
(* ------------------------------------------------------------------------- *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================