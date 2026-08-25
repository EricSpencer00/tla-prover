---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

\* Set of all positions on the N×N grid
Pos == 1..N \X 1..N

\* The eight (or fewer) neighboring positions of a cell p
Neighbors(p) == { q \in Pos :
                    q # p /\ 
                    (Abs(q[1] - p[1]) <= 1) /\ 
                    (Abs(q[2] - p[2]) <= 1) }

\* Number of live neighbors of cell p in the current grid
LiveNeighbors(p) == Cardinality( { q \in Pos : q \in Neighbors(p) /\ grid[q] } )

\* Initial state: any assignment of true/false to every cell
Init == grid \in [Pos -> BOOLEAN]

\* One tick: simultaneous update of all cells
Next == grid' = [p \in Pos |-> 
                  IF grid[p] 
                  THEN (LiveNeighbors(p) = 2) \/ (LiveNeighbors(p) = 3) 
                  ELSE LiveNeighbors(p) = 3]

\* The full specification
Spec == Init /\ [][Next]_<<grid>>

\* Type invariant
TypeOK == grid \in [Pos -> BOOLEAN]

====