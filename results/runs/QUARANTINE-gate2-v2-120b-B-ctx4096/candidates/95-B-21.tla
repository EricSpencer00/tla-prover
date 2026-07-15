----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive definition of Sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

(* The set of valid positions inside the N x N board *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Type invariant: grid maps each position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper that returns 1 for a live neighbor and 0 otherwise,
   safely handling positions outside the board. *)
sc(q) == IF q \notin Pos THEN 0
        ELSE IF grid[q] THEN 1 ELSE 0

(* Number of live neighbors of position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in {-1,0,1}, dy \in {-1,0,1},
                <<dx, dy>> # <<0,0>>}
  IN Sum(sc, {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs})

(* Initial state: any Boolean assignment over the board *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2,3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================