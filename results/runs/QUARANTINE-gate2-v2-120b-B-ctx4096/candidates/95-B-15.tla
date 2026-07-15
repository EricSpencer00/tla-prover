----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The constant N must be a natural number *)
ASSUME N \in Nat

(* A helper definition used by the temporal operator *)
vars == grid

(* Recursive sum over a finite set of positions using a function f *)
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE 
        LET x == CHOOSE y \in S : TRUE
        IN  f[x] + Sum(f, S \ {x})

(* The set of all valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a function that maps every position to
   a Boolean value (TRUE for alive, FALSE for dead) *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Contribution of a single cell to the score of a point p *)
sc(p) == 
    IF (p[1] \notin 1..N) \/ (p[2] \notin 1..N) THEN 0
    ELSE IF grid[p] THEN 0 ELSE 1

(* Number of live neighbours of a position p *)
score(p) == 
    LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}
        points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
    IN Sum(sc, points)

(* Initial state: any assignment of Boolean values to all positions is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition *)
Next == 
    grid' = [p \in Pos |-> 
                IF /\ grid[p] /\ score(p) \in {2, 3}
                   \/ ~grid[p] /\ score(p) = 3
                THEN TRUE
                ELSE FALSE]

(* Full specification *)
Spec == Init /\ [][Next]_vars

=============================================================================