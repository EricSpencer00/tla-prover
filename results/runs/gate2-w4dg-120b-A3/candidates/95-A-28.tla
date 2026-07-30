---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A cell at (i, j) has up to eight neighbors: the cells directly adjacent
\* horizontally, vertically, and diagonally.  Cells outside the grid are
\* treated as dead (value zero) when counting.
VARIABLES grid

vars == <<grid>>

Positions == 1..N

\* Count the live neighbors of cell (i, j) by inspecting all eight directions.
\* The neighbor set is written out explicitly because each neighbor must be
\* checked against the grid bounds N before its value can be trusted.
LiveNeighbors(i, j) ==
  LET v ==
    { grid[p][q] : p \in {i - 1, i, i + 1}, q \in {j - 1, j, j + 1},
                        ~ (p = i /\ q = j), p \in Positions, q \in Positions }
  IN Cardinality(v)

\* One generation of Life is computed entirely from the current grid, slot by
\* slot, so each update is a pure function of the current state.  The model's
\* nondeterministic initial state is the only source of branching.
NextStep(g) ==
  [ i \in Positions |-> [ j \in Positions |->
       IF g[i][j]
         THEN LiveNeighbors(i, j) \in {2, 3}
         ELSE LiveNeighbors(i, j) = 3
  ]]

Init ==
  \E g \in [Positions -> [Positions -> BOOLEAN]] : grid = g

Next ==
  grid' = NextStep(grid)

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Positions -> [Positions -> BOOLEAN]]

====