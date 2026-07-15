------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE grid

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

\* Sum over a finite set S of values obtained from function f.
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE 
        LET x == CHOOSE x \in S : TRUE IN
        f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Scoring of a cell based on its eight neighbours
\* ----------------------------------------------------------------------
nbrs == {<<dx, dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1}, <<dx, dy>> # <<0, 0>>}

\* sc returns 1 for a live cell that is inside the board and 0 otherwise.
sc(p) == 
    IF p \notin Pos THEN 0
    ELSE IF grid[p] THEN 1
    ELSE 0

\* score(p) is the number of live neighbours of position p.
score(p) == 
    LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs} IN
    Sum(sc, points)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Transition relation (the Game of Life rule)
\* ----------------------------------------------------------------------
Next == 
    /\ grid' = [p \in Pos |-> 
                 IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                 THEN TRUE
                 ELSE FALSE]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<grid>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant (kept exactly as the original intent)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================