---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* The set of all positions on the N×N grid. *)
Positions == 1..N X 1..N

(* Two distinct positions are neighbors if they differ by at most 1 in each coordinate. *)
IsNeighbor(p, q) ==
  LET i  == p[1],  j  == p[2],
      ii == q[1],  jj == q[2] IN
    (ii - i) \in -1..1 /\ (jj - j) \in -1..1 /\ ~(ii = i /\ jj = j)

(* Number of live neighbours of position p in the current grid. *)
NeighborCount(p) ==
  Cardinality({ q \in Positions : IsNeighbor(p, q) /\ grid[q] })

(* Initial state: any assignment of true/false to each cell is allowed. *)
Init ==
  grid \in [Positions -> BOOLEAN]

(* Simultaneous update of all cells according to the Game of Life rules. *)
Next ==
  /\ grid' = [p \in Positions |
                LET cnt == NeighborCount(p) IN
                  IF (grid[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~grid[p] /\ cnt = 3)
                  THEN TRUE
                  ELSE FALSE
            ]

(* Full specification: init followed by forever steps of Next. *)
Spec ==
  Init /\ [][Next]_<<grid>>

(* Type invariant ensuring grid always maps positions to booleans. *)
TypeOK ==
  grid \in [Positions -> BOOLEAN]

====