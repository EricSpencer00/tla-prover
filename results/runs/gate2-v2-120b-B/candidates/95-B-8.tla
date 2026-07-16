----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The constant N is constrained to be a natural number. *)
ASSUME N \in Nat

vars == grid

(* Recursive definition to sum a function over a finite set. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* The set of valid positions on the N×N board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper for scoring a cell: 1 for each live neighbor, 0 otherwise. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0
        \/ x > N \/ y > N
        \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* Score of a position p: number of live neighbors. *)
score(p) ==
  LET nbrs  == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial condition: any assignment of dead/alive values to the board. *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition rule. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Full specification: init and temporal evolution. *)
Spec == Init /\ [][Next]_vars

=============================================================================