---- MODULE GameOfLife ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT N \* grid dimension (must be assigned in the .cfg)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Returns the set of neighbor positions for a given cell, staying inside
\* the N x N grid (positions outside are ignored, effectively treated as dead).
Neighbors(p) ==
  LET row == p[1] IN
  LET col == p[2] IN
  { <<r, c>> :
      r \in row-1 .. row+1 /\ c \in col-1 .. col+1 /\
      (r # row \/ c # col) /\ r \in Rows /\ c \in Cols }

\* Number of live neighbors of position p in the current grid.
LiveNeighborCount(p) ==
  Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Positions -> BOOLEAN] \* any mapping of positions to booleans

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
  /\ grid' = [p \in Positions |-> 
        IF grid[p] = TRUE THEN
           /\ (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3)
           TRUE
        ELSE
           /\ LiveNeighborCount(p) = 3
           TRUE
      ]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Tick]_<<grid>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
\* TypeOK ensures that the only state variable is a proper mapping from
\* each grid position to a Boolean (alive or dead).
TypeOK ==
  grid \in [Positions -> BOOLEAN]

====