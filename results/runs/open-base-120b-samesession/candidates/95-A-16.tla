---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES grid

(* The set of all positions on an N×N grid *)
Pos == 1..N \X 1..N

Row(p) == p[1]
Col(p) == p[2]

(* Two positions are neighbors if they differ by at most 1 in each coordinate
   and are not the same position *)
IsNeighbor(p, q) ==
    /\ p # q
    /\ Row(p) - Row(q) \in -1..1
    /\ Col(p) - Col(q) \in -1..1

(* Number of live neighbours of position p in the current grid *)
LiveNeighbors(p) == Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] })

(* Initial state: any assignment of booleans to the cells *)
Init == grid \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells according to the Game of Life rules *)
Next ==
    LET newVal(p) ==
            IF grid[p]
            THEN LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3
            ELSE LiveNeighbors(p) = 3
    IN  grid' = [p \in Pos |-> newVal(p)]

(* Overall specification *)
Spec == Init /\ [][Next]_<<grid>>

(* Type invariant *)
TypeOK == grid \in [Pos -> BOOLEAN]

====