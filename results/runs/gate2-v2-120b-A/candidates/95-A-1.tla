---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N \* grid dimension (must be a natural number)

\* ----------------------------------------------------------------------
\* Types and constants
\* ----------------------------------------------------------------------
Cell == BOOLEAN               \* each cell is either FALSE (dead) or TRUE (alive)
Pos  == 1..N                  \* valid row or column index

\* The set of all positions on the grid
AllPos == Pos \X Pos

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE grid   \* mapping from each position to a Boolean (alive/dead)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Neighbor offsets (including diagonal neighbors)
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,           << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* Neighborhood of a position (positions that are inside the grid)
Neighbors(p) ==
    { <<r + dr, c + dc>> :
        LET r == p[1] IN LET c == p[2] IN
        dr_dc \in NeighborOffsets,
        dr == dr_dc[1], dc == dr_dc[2],
        dr_dc # <<0,0>> /\            \* exclude the position itself
        1 <= r + dr /\ r + dr <= N /\
        1 <= c + dc /\ c + dc <= N }

\* Number of alive neighbors of a position
AliveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

\* Deterministic next state of a single cell
NextCellValue(p) ==
    IF grid[p] THEN
        /\ (AliveNeighbors(p) = 2) \/ (AliveNeighbors(p) = 3)
        THEN TRUE
        ELSE FALSE
    ELSE
        /\ AliveNeighbors(p) = 3
        THEN TRUE
        ELSE FALSE

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [AllPos -> BOOLEAN]   \* any mapping from positions to booleans
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Safety type invariant (required by the cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ grid \in [AllPos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Evolution (Tick action)
\* ----------------------------------------------------------------------
Tick ==
    /\ grid' = [p \in AllPos |-> NextCellValue(p)]
    /\ UNCHANGED << >>   \* no other variables exist

Next == Tick

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

=============================================================================