---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* The set of all cell positions on the N×N board *)
Cell == 1..N \X 1..N

(* The eight neighboring positions of a cell, restricted to the board *)
Neighbors(pos) ==
  { <<i, j>> \in Cell :
        i \in pos[1] - 1 .. pos[1] + 1 /\
        j \in pos[2] - 1 .. pos[2] + 1 /\
        ~(i = pos[1] /\ j = pos[2]) }

(* Number of live (TRUE) neighbors of a cell *)
LiveNeighbors(pos) ==
  Cardinality({ p \in Neighbors(pos) : grid[p] })

(* Initial state: any assignment of TRUE/FALSE to every cell *)
Init ==
  grid \in [Cell -> BOOLEAN]

(* One deterministic update step (the Game of Life rules) *)
Next ==
  /\ grid' = [pos \in Cell |
        IF grid[pos]
           THEN (LiveNeighbors(pos) = 2 \/ LiveNeighbors(pos) = 3)
           ELSE LiveNeighbors(pos) = 3]

(* The overall specification *)
Spec ==
  Init /\ [][Next]_grid

(* Type invariant *)
TypeOK ==
  grid \in [Cell -> BOOLEAN]

====