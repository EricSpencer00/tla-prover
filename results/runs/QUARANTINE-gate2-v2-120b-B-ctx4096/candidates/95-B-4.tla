----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of valid positions inside the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Invariant: each entry of grid must be a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Neighborhood includes the eight surrounding cells *)
nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* Score of a cell p is the number of live neighbours *)
score(p) ==
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(
        [q \in points |-> 
           IF q \in Pos /\ grid[q] THEN 1 ELSE 0],
        points)

(* Initial state: any Boolean assignment to the board *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ 
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================