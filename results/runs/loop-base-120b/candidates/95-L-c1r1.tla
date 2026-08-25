---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* The set of all positions on the N×N grid *)
Cells == (1..N) \X (1..N)

(* A neighbor is any distinct cell within one step horizontally, vertically, or diagonally *)
IsNeighbor(p, q) ==
    p # q /\ 
    Abs(p[1] - q[1]) <= 1 /\ Abs(p[2] - q[2]) <= 1

(* Number of live neighbors of position p in the current grid *)
NeighborCount(p) ==
    Cardinality({ q \in Cells : IsNeighbor(p, q) /\ grid[q] = TRUE })

(* Initial state: each cell may be alive or dead nondeterministically *)
Init ==
    grid \in [Cells -> BOOLEAN]

(* Simultaneous update according to the Game of Life rules *)
Next ==
    grid' = [p \in Cells |-> 
        IF grid[p] 
        THEN (NeighborCount(p) = 2) \/ (NeighborCount(p) = 3)
        ELSE (NeighborCount(p) = 3)
    ]

(* The full specification *)
Spec ==
    Init /\ [][Next]_<<grid>>

(* Type invariant *)
TypeOK ==
    grid \in [Cells -> BOOLEAN]

====