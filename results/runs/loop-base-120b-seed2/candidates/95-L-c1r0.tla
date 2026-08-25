---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

(* The set of positions on the N×N grid *)
Cell == 1..N \X 1..N

VARIABLE grid

(* Type invariant for the state variables and constant N *)
TypeOK == 
  /\ grid \in [Cell -> BOOLEAN]
  /\ N \in Nat
  /\ N > 0

(* Any Boolean assignment to all cells is a possible initial state *)
Init == grid \in [Cell -> BOOLEAN]

(* Neighbor positions of a given cell, staying inside the grid *)
Neighbors(pos) ==
  { p \in Cell :
        (p[1] >= pos[1] - 1) /\ (p[1] <= pos[1] + 1) /\
        (p[2] >= pos[2] - 1) /\ (p[2] <= pos[2] + 1) /\
        p # pos }

(* Number of live (true) neighbors of a cell in the current grid *)
NeighborCount(pos) ==
  Cardinality({ p \in Neighbors(pos) : grid[p] })

(* Simultaneous update of the whole grid according to Game of Life rules *)
Next ==
  grid' = [pos \in Cell |
           LET cnt == NeighborCount(pos) IN
               IF grid[pos] THEN (cnt = 2) \/ (cnt = 3)
               ELSE (cnt = 3)]

(* Full specification: initialization followed by always taking Next steps *)
Spec == Init /\ [][Next]_<<grid>>

====