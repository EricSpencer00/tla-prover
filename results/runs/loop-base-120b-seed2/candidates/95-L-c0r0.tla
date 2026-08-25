---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANT N

VARIABLE Grid

(* The set of all positions on the N×N grid *)
Pos == 1..N X 1..N

(* Two distinct positions are neighbors if each coordinate differs by at most 1 *)
IsNeighbor(p, q) ==
    /\ p # q
    /\ (p[1] - q[1]) \in {-1, 0, 1}
    /\ (p[2] - q[2]) \in {-1, 0, 1}

(* Number of live neighbours of position p in the current state *)
NeighborCount(p) ==
    Cardinality({ q \in Pos : IsNeighbor(p, q) /\ Grid[q] })

(* Any assignment of booleans to the grid is a possible initial state *)
Init ==
    Grid \in [Pos -> BOOLEAN]

(* Simultaneous update according to the Game of Life rules *)
Next ==
    /\ \A p \in Pos :
          IF Grid[p]
          THEN Grid'[p] = (NeighborCount(p) = 2) \/ (NeighborCount(p) = 3)
          ELSE Grid'[p] = (NeighborCount(p) = 3)

(* Full specification *)
Spec ==
    Init /\ [] [Next]_<<Grid>>

(* Type invariant *)
TypeOK ==
    Grid \in [Pos -> BOOLEAN]

====