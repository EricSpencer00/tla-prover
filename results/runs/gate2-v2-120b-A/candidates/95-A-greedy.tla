---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension (must be a natural number)

\* ----------------------------------------------------------------------
\* State variable: a mapping from each grid position to a Boolean
\* indicating whether the cell is alive (TRUE) or dead (FALSE).
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Pos == 1 .. N

AllPos == { [i \in Pos, j \in Pos] }

Neighbors(p) ==
  { [i, j] \in AllPos :
      i # p[1] \/ j # p[2] /\ 
      i \in p[1] - 1 .. p[1] + 1 /\ 
      j \in p[2] - 1 .. p[2] + 1 }

LiveNeighborsCount(g, p) ==
  Cardinality({ q \in Neighbors(p) : g[q] = TRUE })

\* ----------------------------------------------------------------------
\* Initial state: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [AllPos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Deterministic update (Tick) applied simultaneously to all cells
\* ----------------------------------------------------------------------
Next ==
  /\ grid' = [p \in AllPos |-> 
        IF grid[p] = TRUE THEN
            /\ LiveNeighborsCount(grid, p) \in {2, 3}
            TRUE
        ELSE
            /\ LiveNeighborsCount(grid, p) = 3
            TRUE
        ELSE FALSE]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (required by the .cfg)
\* ----------------------------------------------------------------------
TypeOK == grid \in [AllPos -> BOOLEAN]

=============================================================================