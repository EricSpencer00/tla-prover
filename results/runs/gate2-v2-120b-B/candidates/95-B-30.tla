----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

(* Set of valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* The original TypeOK invariant was incorrectly negated.
   The corrected invariant states that every entry of the grid
   must be a Boolean value, i.e., the grid is a total function from
   Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper for scoring cells.  The original definition used a literal
   set of points, which caused a type mismatch.  Here we compute the
   set of neighbor positions explicitly and then apply the recursive
   sum. *)
Nbrs == {<<dx, dy>> : dx, dy \in -1..1 /\ <<dx, dy>> # <<0, 0>>}

sc(p) == IF p \in (0 .. N+1) \X (0 .. N+1) THEN
           IF p \in Pos /\ grid[p] THEN 1 ELSE 0
        ELSE 0

score(p) ==
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in Nbrs}
  IN Sum(sc, points)

(* Initial state: the grid may be any Boolean assignment over Pos. *)
Init == grid \in [Pos -> BOOLEAN]

(* Standard Game of Life transition. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================