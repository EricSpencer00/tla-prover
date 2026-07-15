----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE grid

\* Ensure N is a natural number within the specification.
ASSUME N \in Nat

Pos == {<<x, y>> : x, y \in 1..N}

\* The grid maps each position to a Boolean value (TRUE = alive, FALSE = dead).
\* The original specification used a negated type invariant, which caused
\* the initial state to violate the invariant.  We replace it with a correct
\* type invariant that asserts the intended mapping.
TypeOK == grid \in [Pos -> BOOLEAN]

\* Recursive sum over a finite set of positions.
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

\* The scoring function counts live neighbours, treating cells outside the
\* board as dead.  The original definition used a domain that included
\* out‑of‑bounds positions and a negated condition, which was both
\* unnecessarily complex and source of the type error.  The rewritten
\* version computes the neighbour count directly.
score(p) ==
  LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN
    Cardinality({q \in points : q \in Pos /\ grid[q]})

Init == grid \in [Pos -> BOOLEAN]

Next ==
  grid' = [p \in Pos |-> IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                        THEN TRUE
                        ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

=============================================================================