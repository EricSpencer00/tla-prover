---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}
\* The original invariant claimed that the grid is NOT a mapping from Pos to BOOLEAN,
\* which contradicts the intended model where each cell is either alive (TRUE) or dead (FALSE).
\* The invariant is therefore corrected to assert the intended type.
TypeOK == grid \in [Pos -> BOOLEAN]

\* Neighborhood definition for a cell p
nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

\* Score function counts the number of alive neighbours of p
score(p) ==
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Cardinality({q \in points : q \in Pos /\ grid[q]})

Init == grid \in [Pos -> BOOLEAN]

Next ==
  grid' =
    [p \in Pos |-> 
       IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
       THEN TRUE
       ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================