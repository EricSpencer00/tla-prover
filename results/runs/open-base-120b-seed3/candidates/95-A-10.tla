---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* The set of all positions on the N×N grid *)
Cells == 1..N \X 1..N

(* The eight neighboring positions that lie inside the grid *)
Neighbors(pos) ==
  LET i == pos[1] ,
      j == pos[2] IN
    { << i + di , j + dj >> :
        di \in -1..1 , dj \in -1..1 ,
        /\ ~(di = 0 /\ dj = 0)
        /\ i + di \in 1..N
        /\ j + dj \in 1..N }

(* Number of live neighbours of a given cell *)
NeighborCount(pos) ==
  Cardinality( { q \in Neighbors(pos) : grid[q] } )

(* Initial state: any assignment of true/false to every cell *)
Init ==
  /\ grid \in [Cells -> BOOLEAN]

(* Simultaneous update of all cells according to Game of Life rules *)
Next ==
  /\ grid' = [pos \in Cells |-
        LET cnt == NeighborCount(pos) IN
          IF grid[pos] /\ (cnt = 2 \/ cnt = 3) THEN TRUE
          ELSE IF ~grid[pos] /\ cnt = 3 THEN TRUE
          ELSE FALSE
      ]

(* Type invariant: grid is always a total function from Cells to BOOLEAN *)
TypeOK == grid \in [Cells -> BOOLEAN]

(* The full specification *)
Spec == Init /\ [][Next]_<<grid>>

====