------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

(* The grid variable maps each position to a BOOLEAN indicating whether the
   cell is alive (TRUE) or dead (FALSE). *)
vars == <<grid>>

(* Recursive definition to sum integer values returned by a function f over a
   finite set S. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN
    0
  ELSE
    LET x == CHOOSE y \in S : TRUE IN
      f[x] + Sum(f, S \ {x})

(* The set of all valid positions on the N×N board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type correctness invariant: grid must be a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper for counting live neighbours. The domain of sc is extended to include a
   border of width 1 around the board (indices 0 and N+1).  For positions
   outside the board its value is 0, while for positions inside it reflects the
   state of the corresponding cell. *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  IF x \in 1..N /\ y \in 1..N THEN
    IF grid[<<x, y>>] THEN 1 ELSE 0
  ELSE
    0

(* Score of a position p is the number of live neighbours. *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>} IN
    Sum(sc, {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs})

(* Initial state: every cell is dead.  This satisfies TypeOK. *)
Init ==
  grid = [p \in Pos |-> FALSE]

(* Transition relation: standard Game of Life rules applied to every cell. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
              THEN TRUE
              ELSE FALSE]

(* Full specification: Init holds initially and Next is always taken. *)
Spec == Init /\ [][Next]_vars

=============================================================================