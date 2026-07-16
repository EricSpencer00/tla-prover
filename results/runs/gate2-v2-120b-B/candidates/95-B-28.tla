---- MODULE GameOfLife ----
EXTENDS Integers, Sequences

CONSTANT N
VARIABLE grid

(* The size of the board is assumed to be a natural number. *)
ASSUME N \in Nat

Pos == {<<x, y>> : x, y \in 1..N}

(* 
   The original specification intended the invariant TypeOK to assert that
   'grid' is NOT a total function from Pos to BOOLEAN. This is the opposite
   of what a well‑typed model of Conway's Game of Life requires.
   We therefore replace the buggy invariant with a correct one that
   guarantees that every position on the board has a Boolean value.
*)
TypeOK == grid \in [Pos -> BOOLEAN]

(*------------------------------------------------------------*)
(*  Helper: sum of a function over a finite set                 *)
(*------------------------------------------------------------*)
RECURSIVE Sum(_,_)

Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE IN
    f[x] + Sum(f, S \ {x})

(*------------------------------------------------------------*)
(*  Scoring function for a cell, counting live neighbours       *)
(*------------------------------------------------------------*)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1,0,1} \X {-1,0,1} : <<dx, dy>> # <<0,0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(*------------------------------------------------------------*)
(*  Initialization: any Boolean assignment over the board is   *)
(*  allowed, but it must respect the TypeOK invariant.        *)
(*------------------------------------------------------------*)
Init ==
  /\ grid \in [Pos -> BOOLEAN]
  /\ TypeOK

(*------------------------------------------------------------*)
(*  Next-state relation: standard Game of Life rules          *)
(*------------------------------------------------------------*)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ score(p) \in {2,3})
           \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

vars == <<grid>>

Spec == Init /\ [][Next]_vars

=============================================================================