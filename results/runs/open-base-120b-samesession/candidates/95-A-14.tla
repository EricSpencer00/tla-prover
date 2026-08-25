---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* Neighbor positions of a given cell, staying inside the grid *)
Neighbors(p) == { q \in Pos :
                    (p[1] - q[1]) \in -1..1 /\ 
                    (p[2] - q[2]) \in -1..1 /\ 
                    q # p }

(* Number of live neighbors of cell p *)
LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

(* The deterministic update rule for a single cell *)
Update(p) ==
    IF grid[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3) THEN TRUE
    ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3               THEN TRUE
    ELSE FALSE

(* Initial condition: any assignment of booleans to the grid is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Simultaneous update of the whole grid *)
Next == /\ grid' = [p \in Pos |-> Update(p)]

(* The full specification *)
Spec == Init /\ [][Next]_grid

(* Type invariant *)
TypeOK == grid \in [Pos -> BOOLEAN]

====