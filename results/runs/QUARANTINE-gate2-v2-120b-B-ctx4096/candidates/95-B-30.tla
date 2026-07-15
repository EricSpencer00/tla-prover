---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

\* --------------------------------------------------------------
\* Types
\* --------------------------------------------------------------
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* The neighborhood offsets (excluding the cell itself)
NbrOffsets == {<<dx, dy>> : dx \in {-1, 0, 1},
                               dy \in {-1, 0, 1},
                               <<dx, dy>> # <<0, 0>>}

\* For a point p, the set of its 8 neighboring positions
Neighbors(p) == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in NbrOffsets}

\* Score function: counts living neighbors (cells outside the board are dead)
score(p) ==
  LET pts == {q \in Pos : q \in Neighbors(p)}
  IN Sum([q \in Pos |-> IF grid[q] THEN 1 ELSE 0], pts)

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN]

Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2, 3}) \/
           (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

vars == <<grid>>

Spec == Init /\ [][Next]_vars

\* --------------------------------------------------------------
\* Invariant: variable stays within the defined domain
\* --------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================