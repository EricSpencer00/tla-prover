---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANT N \* grid dimension (N >= 1)

\* ----------------------------------------------------------------------
\* Set of all cell positions (row, column) within the N-by-N grid
Cell == (1..N) \X (1..N)

\* ----------------------------------------------------------------------
\* State variable: mapping each cell to a Boolean (TRUE = alive, FALSE = dead)
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper: are two positions neighbors (including diagonals) ?
IsNeighbor(p, q) == 
    /\ p # q
    /\ ABS(p[1] - q[1]) <= 1
    /\ ABS(p[2] - q[2]) <= 1

\* Number of live neighbours of a cell p in the current grid
LiveNeighbors(p) == 
    Cardinality({ q \in Cell : IsNeighbor(p, q) /\ grid[q] })

\* ----------------------------------------------------------------------
\* Initial state: any assignment of Boolean values to all cells
Init == grid \in [Cell -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Next-state relation: simultaneous update according to Life rules
Next == 
    \A p \in Cell :
        LET n == LiveNeighbors(p) IN
        grid'[p] = 
            IF grid[p] 
                THEN n = 2 \/ n = 3    \* live cell survives with 2 or 3 neighbours
                ELSE n = 3            \* dead cell becomes alive with exactly 3 neighbours

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_grid

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK == grid \in [Cell -> BOOLEAN]

====