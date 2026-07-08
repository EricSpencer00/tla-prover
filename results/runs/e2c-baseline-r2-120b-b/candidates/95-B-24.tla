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
\* The invariant should state that the grid is a function from Pos to BOOLEAN.
TypeOK == grid \in [Pos -> BOOLEAN]

\* Define the score contribution function `sc`.  For positions outside the board
\* (x = 0, y = 0, x > N, or y > N) the contribution is 0.  For positions inside
\* the board the contribution is 0 when the cell is dead and 1 when it is alive.
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
    CASE (x = 0) \/ (y = 0) \/ (x > N) \/ (y > N) -> 0
    [] ~grid[<<x, y>>]                                 -> 0
    [] OTHER                                            -> 1

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