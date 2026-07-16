----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N

VARIABLE grid

(* Ensure N is a natural number *)
ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set of points using the supplied function f *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Corrected type invariant: grid must be a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that assigns a contribution of 0 to out‑of‑bounds or dead
   cells and 1 to live cells. The domain of the function is all points that
   may be examined when scoring a cell. *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  IF x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] THEN 0
  ELSE 1

(* Number of live neighbours of a cell p *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in -1..1 /\ dy \in -1..1 /\ <<dx, dy>> # <<0,0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any Boolean assignment to the board is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Game‑of‑Life transition *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2,3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================