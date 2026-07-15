---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, must be a positive natural number

\* ----------------------------------------------------------------------
\* State variable: mapping each position (i,j) in the N×N grid to a Bool
\* indicating whether the cell is alive (TRUE) or dead (FALSE)
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definition: the set of all valid positions on the grid
\* ----------------------------------------------------------------------
Pos == { i \in 1..N, j \in 1..N }

\* ----------------------------------------------------------------------
\* Type invariant (used as the INVARIANT named TypeOK)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Neighbor positions (including those possibly outside the grid)
\* ----------------------------------------------------------------------
Neighbors(p) ==
    LET i == p[1], j == p[2] IN
    { <<i + di, j + dj>> :
        di \in {-1, 0, 1},
        dj \in {-1, 0, 1},
        (di # 0 \/ dj # 0) }

\* ----------------------------------------------------------------------
\* Count of live neighbors, treating out‑of‑bounds positions as dead
\* ----------------------------------------------------------------------
LiveNeighborCount(p) ==
    Cardinality({ q \in Neighbors(p) :
        /\ q[1] \in 1..N
        /\ q[2] \in 1..N
        /\ grid[q] = TRUE })

\* ----------------------------------------------------------------------
\* Deterministic update rule for a single cell
\* ----------------------------------------------------------------------
NextState(p) ==
    IF grid[p] = TRUE THEN
        (* live cell survives with 2 or 3 live neighbors *)
        IF LiveNeighborCount(p) \in {2, 3} THEN TRUE ELSE FALSE
    ELSE
        (* dead cell becomes alive with exactly 3 live neighbors *)
        IF LiveNeighborCount(p) = 3 THEN TRUE ELSE FALSE

\* ----------------------------------------------------------------------
\* Tick action: simultaneous update of the whole grid
\* ----------------------------------------------------------------------
Tick ==
    /\ grid' = [p \in Pos |-> NextState(p)]

\* ----------------------------------------------------------------------
\* Next-state relation (only the Tick action is allowed)
\* ----------------------------------------------------------------------
Next == Tick

\* ----------------------------------------------------------------------
\* Specification: the usual temporal formula used by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* The historical name expected by the .cfg file for the invariant
\* ----------------------------------------------------------------------
Invariant == TypeOK

\* ----------------------------------------------------------------------
\* Expose the names required by the configuration
\* ----------------------------------------------------------------------
Spec == Spec
TypeOK == TypeOK
======