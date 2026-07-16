---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Pos == {<<x, y>> : x, y \in 1..N}
\* The grid maps each position to a Boolean (TRUE = alive, FALSE = dead)
\* This is the intended type invariant.
gridType == [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Recursive sum over a finite set of positions, using a function that
\* returns a natural number for each position.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_,_)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Score (number of live neighbours) for a given position
\* ----------------------------------------------------------------------
nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0,0>>}

score(p) ==
    LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
    IN
        \* Count only neighbours that lie inside the board
        Sum(
            LAMBDA q \in Pos : IF q \in points /\ grid[q] THEN 1 ELSE 0,
            points \cap Pos)

\* ----------------------------------------------------------------------
\* Initial state and transition relation
\* ----------------------------------------------------------------------
Init == grid \in gridType

Next ==
    grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2, 3}) \/
                   (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<grid>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant describing the intended type of the mutable variable
\* ----------------------------------------------------------------------
TypeOK == grid \in gridType

=============================================================================