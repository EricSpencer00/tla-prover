---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* Variables set for stuttering *)
vars == grid

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_,_)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of valid positions inside the N×N board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Corrected type invariant: grid must be a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper that contributes 1 for a live neighbor, 0 otherwise, but only
   for positions that lie inside the board. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE
    \/ x = 0 \/ y = 0 \/ x > N \/ y > N -> 0
    [] ~grid[<<x, y>>] -> 0
    [] OTHER -> 1

(* Number of live neighbors of position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1,0,1} \X {-1,0,1} : <<dx, dy>> # <<0,0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any Boolean assignment to the board, respecting TypeOK *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2,3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_vars

====