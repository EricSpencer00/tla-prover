----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum over a set S of positions, applying function f to each element. *)
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE 
         IN f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}

(* The intended type invariant: grid is a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper: treat cells outside the board as dead (value 0). *)
sc(p) == 
    IF p \notin Pos THEN 0
    ELSE IF ~grid[p] THEN 0
    ELSE 1

(* Number of live neighbours of position p. *)
score(p) == 
    LET nbrs == {<<dx, dy>> : dx \in -1..1 /\ dy \in -1..1 /\ <<dx, dy>> # <<0, 0>>}
        points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
    IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

(* Standard Game of Life transition. *)
Next == 
    grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================