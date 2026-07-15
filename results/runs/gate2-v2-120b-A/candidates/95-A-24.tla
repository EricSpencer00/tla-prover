---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N \* grid dimension, to be supplied in the .cfg file

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rows == 1..N
Cols == 1..N
Positions == [r \in Rows |-> [c \in Cols |-> <<r, c>>]]
Cell == BOOLEAN

\* The set of all grid positions
Pos == { <<r, c>> : r \in Rows, c \in Cols }

\* Returns the value of a cell, treating positions outside the grid as FALSE
CellVal(pos) ==
  IF pos \in Pos THEN grid[pos] ELSE FALSE

\* The eight neighboring offsets (including diagonals)
NeighborOffsets == { <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
                     << 0, -1>>,           << 0, 1>>,
                     << 1, -1>>, << 1, 0>>, << 1, 1>> }

\* The set of neighbor positions for a given position
Neighbors(pos) ==
  { <<pos[1] + dr, pos[2] + dc>> :
      <<dr, dc>> \in NeighborOffsets }

\* Number of live neighbors of a position
LiveNeighborCount(pos) ==
  Cardinality({ n \in Neighbors(pos) : CellVal(n) = TRUE })

\* ----------------------------------------------------------------------
\* State transition (the Game of Life rule)
\* ----------------------------------------------------------------------
Tick ==
  /\ grid' = [p \in Pos |-> 
               IF grid[p] = TRUE THEN
                 (* live cell survives with 2 or 3 live neighbors *)
                 IF LiveNeighborCount(p) \in {2, 3} THEN TRUE ELSE FALSE
               ELSE
                 (* dead cell becomes alive with exactly 3 live neighbors *)
                 IF LiveNeighborCount(p) = 3 THEN TRUE ELSE FALSE ]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN] \* each cell nondeterministically alive or dead

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Next == Tick

Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================