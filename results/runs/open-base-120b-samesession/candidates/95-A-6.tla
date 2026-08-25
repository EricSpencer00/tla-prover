---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE grid

(* The set of all cell positions on the N×N grid *)
Cell == 1..N \X 1..N

(* Neighboring positions of a cell, staying within the grid *)
Neighbors(p) == {
    q \in Cell :
        /\ q[1] \in (p[1] - 1) .. (p[1] + 1)
        /\ q[2] \in (p[2] - 1) .. (p[2] + 1)
        /\ q # p
}

(* Number of live (true) neighbors of a cell *)
LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

(* Initial state: any assignment of true/false to each cell *)
Init == grid \in [Cell -> BOOLEAN]

(* Simultaneous update according to Conway's rules *)
Next == 
    /\ \A p \in Cell :
        LET cnt == LiveNeighborCount(p) IN
        grid' [p] = IF grid[p] 
                     THEN (cnt = 2) \/ (cnt = 3) 
                     ELSE (cnt = 3)

(* Overall specification *)
Spec == Init /\ [][Next]_grid

(* Type invariant *)
TypeOK == grid \in [Cell -> BOOLEAN]

====