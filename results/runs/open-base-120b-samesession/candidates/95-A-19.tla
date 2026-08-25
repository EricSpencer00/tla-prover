---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

CellIdx == 1..N
Cell    == CellIdx \X CellIdx

(* A neighbor is any distinct cell at most one step away horizontally,
   vertically, or diagonally. Cells outside the grid are simply not
   included in the set of cells, so they are treated as dead. *)
IsNeighbor(p, q) ==
    /\ p # q
    /\ (p[1] - q[1]) \in {-1, 0, 1}
    /\ (p[2] - q[2]) \in {-1, 0, 1}

NeighborCount(p) ==
    Cardinality({ q \in Cell : IsNeighbor(p, q) /\ grid[q] })

Init ==
    /\ grid \in [Cell -> BOOLEAN]

Next ==
    /\ grid' = [p \in Cell |-> 
          LET n == NeighborCount(p) IN
          IF grid[p] 
             THEN (n = 2) \/ (n = 3) 
             ELSE (n = 3)
       ]

TypeOK ==
    /\ grid \in [Cell -> BOOLEAN]

Spec == Init /\ [][Next]_<<grid>>

====