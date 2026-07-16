---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* N is a natural number, as required by the model. *)
ASSUME N \in Nat

vars == grid

(* Recursive definition of a generic sum over a finite set. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE IN
      f[x] + Sum(f, S \ {x})

(* The set of positions that belong to the N-by-N board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that assigns a score contribution to a single cell. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  IF \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] THEN 0
  ELSE 1

(* The number of live neighbours of position p. *)
score(p) ==
  LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x # <<0, 0>>} IN
    Sum(sc, {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs})

(* Initial state: any assignment of Boolean values to the board is allowed. *)
Init == grid \in [Pos -> BOOLEAN]

(* Standard Game of Life transition. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Full specification. *)
Spec == Init /\ [][Next]_vars

====