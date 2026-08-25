---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

(* The set of positions on the N-by-N grid *)
Pos == (1..N) \X (1..N)

VARIABLE grid

(* Absolute value for integer differences *)
Abs(x) == IF x >= 0 THEN x ELSE -x

(* Two distinct positions are neighbors if they differ by at most one in each coordinate *)
IsNeighbor(p, q) ==
  LET pr == p[1], pc == p[2],
      qr == q[1], qc == q[2]
  IN  p # q /\ Abs(pr - qr) <= 1 /\ Abs(pc - qc) <= 1

(* Number of live neighbours of position p *)
NeighborCount(p) ==
  Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] })

(* Update rule for a single cell *)
Update(p) ==
  IF grid[p] THEN (NeighborCount(p) = 2) \/ (NeighborCount(p) = 3)
            ELSE NeighborCount(p) = 3

(* Initial state: any assignment of true/false to each cell *)
Init ==
  grid \in [Pos -> BOOLEAN]

(* Simultaneous update of all cells *)
Next ==
  /\ grid' = [p \in Pos |-> Update(p)]

(* Full specification *)
Spec ==
  Init /\ [][Next]_<<grid>>

(* Type invariant *)
TypeOK ==
  grid \in [Pos -> BOOLEAN]

====