---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(*--------------------------------------------------------------------
  Pos  : the set of all positions on the N-by-N grid.
--------------------------------------------------------------------*)
Pos == 1..N X 1..N

(*--------------------------------------------------------------------
  Helper to compute absolute difference of two natural numbers.
--------------------------------------------------------------------*)
AbsDiff(a, b) == IF a >= b THEN a - b ELSE b - a

(*--------------------------------------------------------------------
  Two positions are neighbors if they are distinct and their coordinates
  differ by at most 1 in each dimension.
--------------------------------------------------------------------*)
IsNeighbor(p, q) ==
    /\ p # q
    /\ AbsDiff(p[1], q[1]) <= 1
    /\ AbsDiff(p[2], q[2]) <= 1

(*--------------------------------------------------------------------
  Number of live neighbours of position p in the current grid.
--------------------------------------------------------------------*)
NeighborCount(p) ==
    Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] = TRUE })

(*--------------------------------------------------------------------
  The deterministic next state of a cell at position p.
--------------------------------------------------------------------*)
LiveNext(p) ==
    LET cnt == NeighborCount(p) IN
        IF grid[p] THEN cnt = 2 \/ cnt = 3 ELSE cnt = 3

(*--------------------------------------------------------------------
  Initialisation: any assignment of true/false to every cell.
--------------------------------------------------------------------*)
Init == grid \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------
  One simultaneous update of the whole grid.
--------------------------------------------------------------------*)
Next ==
    /\ grid' = [p \in Pos |-> LiveNext(p)]

(*--------------------------------------------------------------------
  Full specification.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<grid>>

(*--------------------------------------------------------------------
  Invariant stating the type of the state variable.
--------------------------------------------------------------------*)
TypeOK == grid \in [Pos -> BOOLEAN]

====