---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N \* grid dimension (to be instantiated in the .cfg)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rows == 1 .. N
Cols == 1 .. N
Pos  == [r \in Rows, c \in Cols]

\* Set of the eight possible neighbor offsets
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,           << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Type invariant (provided as the required INVARIANT)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initialization: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init == /\ grid \in [Pos -> BOOLEAN]
        /\ TRUE   \* no additional constraints; any mapping is allowed

\* ----------------------------------------------------------------------
\* Neighbor counting (cells outside the grid are treated as dead)
\* ----------------------------------------------------------------------
Neighbors(p) == { [r = p.r + d[1], c = p.c + d[2]] :
                    d \in NeighborOffsets,
                    1 <= p.r + d[1] <= N,
                    1 <= p.c + d[2] <= N }

LiveNeighborCount(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] = TRUE })

\* ----------------------------------------------------------------------
\* Update rule for a single cell
\* ----------------------------------------------------------------------
NextValue(p) ==
    IF grid[p] = TRUE THEN
        /\ (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3)
        TRUE
    ELSE
        LiveNeighborCount(p) = 3

\* ----------------------------------------------------------------------
\* Global next-state relation (simultaneous update)
\* ----------------------------------------------------------------------
Next ==
    /\ \A p \in Pos : grid[p] = NextValue(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

====