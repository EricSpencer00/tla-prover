---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N \* grid dimension (N x N)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES A

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Cell == 0 .. N-1

Pos == [i \in Cell, j \in Cell]

\* All possible neighbor offsets (including diagonals)
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,           << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* All positions that are inside the grid
Neighbors(p) ==
    { [i \in Cell, j \in Cell] :
        /\ i = p["i"] + delta[1]
        /\ j = p["j"] + delta[2]
        /\ delta \in NeighborOffsets }

\* Number of live neighbors for a position
LiveNeighborCount(p) ==
    Cardinality({ q \in Neighbors(p) : A[q] = TRUE })

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ A \in [Pos -> BOOLEAN]
    /\ \A p \in Pos: A[p] \in {TRUE, FALSE}

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
    /\ A' \in [Pos -> BOOLEAN]
    /\ \A p \in Pos:
        IF A[p] = TRUE THEN
            (* Live cell survives with 2 or 3 live neighbors *)
            A'[p] = (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3)
        ELSE
            (* Dead cell becomes alive with exactly 3 live neighbors *)
            A'[p] = (LiveNeighborCount(p) = 3)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Tick]_<<A>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == A \in [Pos -> BOOLEAN]

=============================================================================