---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid is a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* scoring function for a cell, handling border cells *)
sc(p) ==
    IF (p[1] = 0) \/ (p[2] = 0) \/ (p[1] > N) \/ (p[2] > N) THEN 0
    ELSE IF ~grid[p] THEN 0
    ELSE 1

score(p) ==
    LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
        points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
    IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================