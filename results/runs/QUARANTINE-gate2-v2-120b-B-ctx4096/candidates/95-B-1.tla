---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

\* The original definition of TypeOK was the opposite of the intended type
\* predicate.  It required that the grid NOT be a function from positions to
\* Boolean values, which is contradictory to the rest of the specification.
\* The invariant is therefore corrected to assert that the grid IS such a
\* function.
TypeOK == grid \in [Pos -> BOOLEAN]

Pos == {<<x, y>> : x, y \in 1..N}

RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

\* The original `sc` definition used a domain that included coordinates
\* outside the board, which caused a type error when the function was
\* applied to a point not in `grid`.  We restrict `sc` to the board,
\* returning 0 for dead cells and 1 for live cells.
sc[p \in Pos] == IF ~grid[p] THEN 0 ELSE 1

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