---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N \* grid dimension (provided by .cfg)

\* ----------------------------------------------------------------------
\* State variable: mapping each position (i,j) to a Boolean (TRUE = alive)
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Derived set of all valid positions on the N-by-N grid
\* ----------------------------------------------------------------------
Pos == 1..N

\* ----------------------------------------------------------------------
\* Helper: the eight neighboring offsets
\* ----------------------------------------------------------------------
NeighborOffsets == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
                    << 0, -1>>,           << 0, 1>>,
                    << 1, -1>>, << 1, 0>>, << 1, 1>>}

\* ----------------------------------------------------------------------
\* Helper: compute the number of live neighbors of a cell (i,j)
\*   Cells outside the grid are treated as dead.
\* ----------------------------------------------------------------------
LiveNeighbors(i, j) ==
  LET nbrs == { <<i + di, j + dj>> :
                 <<di, dj>> \in NeighborOffsets } IN
  Cardinality( { p \in nbrs :
                   /\ 1 <= p[1] /\ p[1] <= N
                   /\ 1 <= p[2] /\ p[2] <= N
                   /\ grid[p] = TRUE } )

\* ----------------------------------------------------------------------
\* Initial state: every cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
  /\ grid = [pos \in Pos \X Pos |-> FALSE]  \* start with all dead
  /\ \A p \in Pos \X Pos : grid[p] \in {TRUE, FALSE}
  /\ \E g \in [Pos \X Pos -> BOOLEAN] : grid = g   \* allow any assignment

\* ----------------------------------------------------------------------
\* Tick action: simultaneous update of all cells according to Game of Life rules
\* ----------------------------------------------------------------------
Tick ==
  /\ grid' = [p \in Pos \X Pos |-> 
               LET i == p[1] IN LET j == p[2] IN
               LET n == LiveNeighbors(i, j) IN
                 IF grid[p] = TRUE THEN
                   (n = 2) \/ (n = 3)
                 ELSE
                   n = 3]

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock when N = 0 (though N > 0 is assumed)
\* ----------------------------------------------------------------------
Stutter ==
  /\ UNCHANGED grid

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ Tick
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness (every entry is a Boolean)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos \X Pos -> BOOLEAN]

=============================================================================