---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
CellSet == { <<i, j>> : i \in 1..N, j \in 1..N }

Abs(x) == IF x >= 0 THEN x ELSE -x

(* Two positions are neighbors if they differ by at most 1 in each coordinate and are not the same cell *)
IsNeighbor(p, q) ==
    /\ p # q
    /\ Abs(p[1] - q[1]) <= 1
    /\ Abs(p[2] - q[2]) <= 1

(* Number of live neighbors of position p in the current grid *)
LiveNeighbors(p) ==
    Cardinality({ q \in CellSet : IsNeighbor(p, q) /\ grid[q] })

(* Initial state: each cell may be alive or dead arbitrarily *)
Init ==
    grid \in [CellSet -> BOOLEAN]

(* Simultaneous update of all cells according to the Game of Life rules *)
Next ==
    /\ grid' = [p \in CellSet |
          IF grid[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3) THEN TRUE
          ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3 THEN TRUE
          ELSE FALSE
       ]

(* Full specification of the system *)
Spec ==
    Init /\ [][Next]_<<grid>>

(* Type invariant: grid always maps each position to a Boolean value *)
TypeOK ==
    grid \in [CellSet -> BOOLEAN]

====