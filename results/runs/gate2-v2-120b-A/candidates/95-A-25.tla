---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N \* grid dimension, must be a positive natural number

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Cells == 1 .. N

Cell == [row : Cells, col : Cells]

\* The set of all positions on the grid
Positions == Cell

\*--------------------------------------------------------------------
\* State variable
\*--------------------------------------------------------------------
VARIABLES grid

\*--------------------------------------------------------------------
\* Type definitions
\*--------------------------------------------------------------------
CellSet == Positions

\* Mapping from each position to a Boolean (TRUE = alive, FALSE = dead)
Grid == [pos \in CellSet -> BOOLEAN]

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ grid \in Grid
    /\ \A pos \in CellSet: grid[pos] \in {TRUE, FALSE}

\*--------------------------------------------------------------------
\* Neighbor calculation (fixed boundaries: outside cells are dead)
\*--------------------------------------------------------------------
Neighbors(pos) ==
    { [row |-> r, col |-> c] :
        /\ r # pos.row
        /\ c # pos.col
        /\ r \in 1..N
        /\ c \in 1..N
        /\ Abs(r - pos.row) <= 1
        /\ Abs(c - pos.col) <= 1 }

LiveNeighborCount(pos) ==
    Cardinality({ n \in Neighbors(pos) : grid[n] = TRUE })

\*--------------------------------------------------------------------
\* Update rule (Tick)
\*--------------------------------------------------------------------
Tick ==
    /\ grid' =
        [pos \in CellSet |-> 
            IF grid[pos] = TRUE THEN
                (* live cell survives with 2 or 3 live neighbors *)
                (LiveNeighborCount(pos) = 2) \/ (LiveNeighborCount(pos) = 3)
            ELSE
                (* dead cell becomes alive with exactly 3 live neighbors *)
                (LiveNeighborCount(pos) = 3)]

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next == Tick

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\*--------------------------------------------------------------------
\* Invariant: all variables stay within their declared types
\*--------------------------------------------------------------------
TypeOK == /\ grid \in Grid
          /\ \A pos \in CellSet: grid[pos] \in BOOLEAN

\*--------------------------------------------------------------------
\* Theorem (optional, not required by cfg but useful)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeOK

====