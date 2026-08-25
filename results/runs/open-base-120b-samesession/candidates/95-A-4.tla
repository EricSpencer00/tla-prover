---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE grid

(* The set of all valid cell positions on the N×N grid *)
CellPos == 1..N \X 1..N

(* Absolute value of an integer *)
Abs(x) == IF x >= 0 THEN x ELSE -x

(* Predicate that p and q are distinct neighboring positions *)
IsNeighbor(p, q) ==
  /\ p # q
  /\ Abs(p[1] - q[1]) <= 1
  /\ Abs(p[2] - q[2]) <= 1

(* Number of live neighbors of position p in the current grid *)
LiveNeighborCount(p) ==
  Cardinality({ q \in CellPos : IsNeighbor(p, q) /\ grid[q] })

(* Initial state: any assignment of true/false to each cell *)
Init ==
  grid \in [CellPos -> BOOLEAN]

(* One synchronous update step according to the Game of Life rules *)
Next ==
  /\ grid' = [p \in CellPos |-> 
        LET n == LiveNeighborCount(p) IN
          IF grid[p] THEN (n = 2) \/ (n = 3) ELSE (n = 3)
     ]

(* Full specification: initialization followed by always taking Next steps *)
Spec == Init /\ [][Next]_grid

(* Type invariant ensuring grid always maps positions to booleans *)
TypeOK == grid \in [CellPos -> BOOLEAN]

====