---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, supplied by the .cfg

\* The set of all valid grid positions (row, column) pairs.
Pos == 1..N

\* State variable representing the whole grid.
\* grid[pos] = TRUE  means the cell at position pos is alive.
\* grid[pos] = FALSE means the cell is dead.
VARIABLE grid

\* A helper to compute the eight neighbor positions of a given cell.
Neighbors(pos) ==
  LET row == pos[1], col == pos[2] IN
  { <<r, c>> :
      r \in {row-1, row, row+1} /\ c \in {col-1, col, col+1} /\ 
      (r # row \/ c # col) /\ r \in Pos /\ c \in Pos }

\* Number of live neighbors of a cell in the current grid.
LiveNeighborCount(pos) ==
  Cardinality({ nb \in Neighbors(pos) : grid[nb] })

\* The deterministic update rule for a single cell.
CellNextAlive(pos) ==
  IF grid[pos] THEN
    LiveNeighborCount(pos) \in {2, 3}
  ELSE
    LiveNeighborCount(pos) = 3

\* Initialization: each cell is nondeterministically alive or dead.
Init ==
  /\ grid = [pos \in Pos X Pos |-> FALSE] \* start from all dead
  /\ \E assign \in [Pos X Pos -> BOOLEAN] :
        grid = assign

\* The Tick action: simultaneous update of all cells.
Tick ==
  /\ grid' = [pos \in Pos X Pos |-> CellNextAlive(pos)]

\* The overall next-state relation, allowing only Tick.
Next == Tick

\* The specification of the system.
Spec == Init /\ [][Next]_grid

\* Type correctness invariant: every entry of grid is a Boolean.
TypeOK == grid \in [Pos X Pos -> BOOLEAN]

====