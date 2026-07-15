---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rows == 1 .. N
Cols == 1 .. N
Pos  == [r \in Rows, c \in Cols |-> <<r, c>>]
AllPos == { p \in Pos : TRUE }

\* The eight possible neighbor offsets
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,            << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* A neighbor is any position offset by one of the NeighborOffsets,
\* provided the resulting position stays inside the grid.
Neighbors(p) ==
    { [r |-> p["r"] + d[1], c |-> p["c"] + d[2]] :
        d \in NeighborOffsets,
        p["r"] + d[1] \in Rows,
        p["c"] + d[2] \in Cols }

\* The number of live (TRUE) neighbors of position p in the current grid
LiveNeighborCount(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [Pos -> BOOLEAN]
    /\ \A p \in Pos: grid[p] \in {TRUE, FALSE}

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
    /\ grid' = [p \in Pos |-> 
            IF grid[p] THEN
                LiveNeighborCount(p) \in {2, 3}
            ELSE
                LiveNeighborCount(p) = 3
        ]
    /\ UNCHANGED << >>  \* No other variables

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Tick]_<<grid>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====