---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == <<grid>>

(* Recursive sum of function values over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* Set of valid positions on the board *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* The original TypeOK was incorrectly defined.  It should assert that
   every element of the state variable `grid` is a Boolean value. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper that maps a (possibly out‑of‑bounds) coordinate to a contribution
   of 0 or 1, without referring to the out‑of‑bounds entry. *)
Sc(p) ==
    IF p \notin Pos THEN 0
    ELSE IF grid[p] THEN 1 ELSE 0

(* Number of live neighbours of position p *)
score(p) ==
    LET nbrs == {<<dx, dy>> : dx \in {-1,0,1}, dy \in {-1,0,1},
                  <<dx, dy>> # <<0,0>>}
    IN Sum(Sc, {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs})

(* Initial state: any Boolean assignment to all positions is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Transition relation implementing the Game of Life rules *)
Next ==
    grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2,3}) \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

=============================================================================