---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

vars == <<grid>>

Pos == 1..N
Positions == Pos \X Pos
Neighbors == Positions

\* Count live neighbors of a cell, treating positions outside the grid as dead.
LiveNeighbors(c) ==
  LET nrs == {
    <<i, j>> \in {{c[1] - 1, c[2] - 1}, {c[1] - 1, c[2]}, {c[1] - 1, c[2] + 1},
                   {c[1], c[2] - 1},                     {c[1], c[2] + 1},
                   {c[1] + 1, c[2] - 1}, {c[1] + 1, c[2]}, {c[1] + 1, c[2] + 1}}
    \cap Positions
  } IN Cardinality({x \in nrs : grid[x]})

TypeOK ==
  /\ grid \in [Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions -> BOOLEAN]

\* Every cell updates simultaneously based on the current neighborhood counts.
Tick ==
  /\ grid' = [c \in Positions |-> IF grid[c]
                     THEN LiveNeighbors(c) \in {2, 3}
                     ELSE LiveNeighbors(c) = 3]

Spec == Init /\ [][Tick]_vars

====