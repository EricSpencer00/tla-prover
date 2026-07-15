---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, Naturals

CONSTANT N

\* The set of valid positions on the N×N board
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

VARIABLE grid

\* -------------------------------------------------------------------------
\* Recursive definition of the sum of a function over a finite set.
\* It is defined only for non‑empty sets, matching the intended usage.
\* -------------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* -------------------------------------------------------------------------
\* Type predicate: grid must be a total mapping from Pos to BOOLEAN.
\* The original specification used a negated type predicate, which caused
\* the invariant to be violated at the initial state.  The corrected predicate
\* asserts the intended type directly.
\* -------------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

\* -------------------------------------------------------------------------
\* Helper that determines whether a cell is alive (1) or dead (0),
\* used for counting live neighbours.  Cells outside the board are treated
\* as dead.
\* -------------------------------------------------------------------------
sc(p) ==
  IF p \in Pos /\ grid[p] THEN 1 ELSE 0

\* -------------------------------------------------------------------------
\* Number of live neighbours of position p.
\* -------------------------------------------------------------------------
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in -1..1, dy \in -1..1, <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

\* -------------------------------------------------------------------------
\* Initial state: any total mapping from Pos to BOOLEAN (alive or dead).
\* -------------------------------------------------------------------------
Init == grid \in [Pos -> BOOLEAN]

\* -------------------------------------------------------------------------
\* Transition relation implementing the Game of Life rules.
\* -------------------------------------------------------------------------
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

\* -------------------------------------------------------------------------
\* Full specification.
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

=============================================================================