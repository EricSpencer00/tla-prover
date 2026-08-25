---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

\* The set of all cell positions on the N-by-N grid
CellSet == 1..N \X 1..N

\* Absolute value for integers (used for neighbor distance)
Abs(x) == IF x >= 0 THEN x ELSE -x

\* The eight (or fewer) neighbors of a cell, staying inside the grid.
Neighbors(p) == 
    { q \in CellSet :
        q # p /\ 
        Abs(p[1] - q[1]) <= 1 /\ 
        Abs(p[2] - q[2]) <= 1 }

VARIABLES grid

\* Type invariant: grid is a total mapping from CellSet to Booleans
TypeOK == grid \in [CellSet -> BOOLEAN]

\* Any assignment of alive/dead to each cell is allowed initially
Init == grid \in [CellSet -> BOOLEAN]

\* One synchronous update of the whole grid
Next == 
    /\ grid' = [p \in CellSet |-> 
                  LET cnt == Cardinality({ q \in Neighbors(p) : grid[q] }) IN
                  ( (grid[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~grid[p] /\ cnt = 3) )]

\* The full specification
Spec == Init /\ [][Next]_<<grid>>

====