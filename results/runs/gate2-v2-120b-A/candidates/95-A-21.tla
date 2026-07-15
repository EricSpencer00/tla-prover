---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N \* grid dimension (N-by-N)

VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Cell == 1 .. N
Pos  == [i : Cell, j : Cell]        \* a grid position
Neighbors(p) == 
    { [i |-> i', j |-> j'] : 
        i' \in Cell, j' \in Cell,
        /\ i' # p.i \/ j' # p.j               \* exclude the cell itself
        /\ Abs(i' - p.i) <= 1
        /\ Abs(j' - p.j) <= 1 }

LiveNeighbors(p, g) == 
    Cardinality({ n \in Neighbors(p) : g[n] })

\* ----------------------------------------------------------------------
\* Type correctness invariant (required as TypeOK)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init == 
    /\ grid = [p \in Pos |-> CHOOSE b \in BOOLEAN : TRUE]

\* ----------------------------------------------------------------------
\* One deterministic step (Tick) for the whole grid
\* ----------------------------------------------------------------------
Tick == 
    /\ grid' = [p \in Pos |-> 
        LET n == LiveNeighbors(p, grid) IN
        IF grid[p] 
            THEN (n = 2) \/ (n = 3)   \* live cell survives with 2 or 3 neighbors
            ELSE (n = 3)               \* dead cell becomes alive with exactly 3
    ]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Tick

\* ----------------------------------------------------------------------
\* Spec (the required SPECIFICATION identifier)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Liveness and safety properties are not specified in the description.
\* ----------------------------------------------------------------------
\* The configuration file will refer to the invariant TypeOK.

=============================================================================