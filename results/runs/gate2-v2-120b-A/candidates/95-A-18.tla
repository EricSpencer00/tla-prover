---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N \* grid dimension (must be a positive integer)

VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Cell == 1 .. N

Pos == [row : Cell, col : Cell]

Neighbors(p) ==
  { [row |-> r, col |-> c] :
      r \in Cell, c \in Cell,
      (r # p.row \/ c # p.col) /\ 
      Abs(r - p.row) <= 1 /\ Abs(c - p.col) <= 1 }

LiveNeighbors(g, p) ==
  Cardinality({ q \in Neighbors(p) : g[q] })

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state: each cell nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN]
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Evolution (Tick) – simultaneous update of all cells
\* ----------------------------------------------------------------------
Tick ==
  \E newGrid \in [Pos -> BOOLEAN] :
    /\ \A p \in Pos :
         LET cnt == LiveNeighbors(grid, p) IN
         newGrid[p] =
           IF grid[p] THEN
              cnt = 2 \/ cnt = 3
           ELSE
              cnt = 3
    /\ grid' = newGrid

\* ----------------------------------------------------------------------
\* Next-state relation (only Tick is allowed)
\* ----------------------------------------------------------------------
Next ==
  Tick

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Declare the identifiers required by the .cfg
\* ----------------------------------------------------------------------
INVARIANT TypeOK

====