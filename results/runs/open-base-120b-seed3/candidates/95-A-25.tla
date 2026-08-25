---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
CellPos == 1..N \X 1..N

(* Offsets for the eight neighboring cells *)
Offsets == {<<dx, dy>> \in -1..1 \X -1..1 : ~(dx = 0 /\ dy = 0)}

(* Number of live neighbours of a given position *)
LiveNeighbors(pos) ==
  LET i == pos[1];
      j == pos[2];
      nbrs == { <<i+dx, j+dy>> :
                 <<dx, dy>> \in Offsets
                 /\ 1 <= i+dx /\ i+dx <= N
                 /\ 1 <= j+dy /\ j+dy <= N }
  IN  Cardinality({p \in nbrs : grid[p]})

(* Initial state: any assignment of booleans to the grid cells *)
Init ==
  /\ grid \in [CellPos -> BOOLEAN]

(* Simultaneous update according to Conway's rules *)
Next ==
  /\ grid' = [pos \in CellPos |
        IF grid[pos]
           THEN (LiveNeighbors(pos) = 2 \/ LiveNeighbors(pos) = 3)
           ELSE (LiveNeighbors(pos) = 3)
      ]

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

(* Type invariant *)
TypeOK == grid \in [CellPos -> BOOLEAN]

====