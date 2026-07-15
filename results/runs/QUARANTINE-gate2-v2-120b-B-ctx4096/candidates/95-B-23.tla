----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers, Naturals

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

Pos == {<<x, y>> : x, y \in 1..N}

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* The intended type invariant: grid maps each position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper that counts live neighbours for a given position p *)
Nbrs == {<<dx, dy>> : dx, dy \in -1..1 /\ <<dx, dy>> # <<0, 0>>}

score(p) ==
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in Nbrs}
  IN
    Cardinality({q \in points : q \in Pos /\ grid[q]})

(* Initial state: any Boolean assignment to the positions is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

=============================================================================