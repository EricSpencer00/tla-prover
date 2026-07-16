----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* Ensure N is a natural number. *)
ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set S using function f. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of positions on the toroidal grid (1..N x 1..N). *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Invariant that the grid maps each position to a Boolean value. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that returns 1 for a live cell and 0 otherwise,
   for positions possibly outside the grid (treated as dead). *)
sc(p) ==
  IF p \notin Pos THEN 0
  ELSE IF grid[p] THEN 1
  ELSE 0

(* Number of live neighbours of position p (the usual Game of Life rules). *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1},
                <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any Boolean assignment to the grid is allowed. *)
Init == grid \in [Pos -> BOOLEAN]

(* Evolution: apply the Game of Life rule to every cell simultaneously. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================