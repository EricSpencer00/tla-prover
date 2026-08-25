---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

(*-----------------------------------------------------------------
   Positions on the N-by-N grid
 -----------------------------------------------------------------*)
Pos == 1..N \X 1..N

VARIABLES grid

(*-----------------------------------------------------------------
   Type invariant: grid maps each position to a Boolean value
 -----------------------------------------------------------------*)
TypeOK == grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
   Initial state: any Boolean assignment to the grid is allowed
 -----------------------------------------------------------------*)
Init == TypeOK

(*-----------------------------------------------------------------
   Absolute value for integer differences
 -----------------------------------------------------------------*)
Abs(i) == IF i >= 0 THEN i ELSE -i

(*-----------------------------------------------------------------
   Predicate that two positions are (distinct) neighbors
 -----------------------------------------------------------------*)
Neighbor(p, q) ==
  LET rp == p[1], cp == p[2],
      rq == q[1], cq == q[2] IN
    (p /= q) /\ Abs(rp - rq) <= 1 /\ Abs(cp - cq) <= 1

(*-----------------------------------------------------------------
   Number of live neighbours of position p in the current grid
 -----------------------------------------------------------------*)
NeighborCount(p) ==
  Cardinality({ q \in Pos : Neighbor(p, q) /\ grid[q] = TRUE })

(*-----------------------------------------------------------------
   Deterministic update rule for a single cell
 -----------------------------------------------------------------*)
NewVal(p) ==
  IF grid[p] = TRUE THEN
    (NeighborCount(p) = 2) \/ (NeighborCount(p) = 3)
  ELSE
    (NeighborCount(p) = 3)

(*-----------------------------------------------------------------
   Simultaneous update of the whole grid (the Tick action)
 -----------------------------------------------------------------*)
Next ==
  /\ grid' = [p \in Pos |-> NewVal(p)]

(*-----------------------------------------------------------------
   Full specification: start in Init and repeatedly take Next steps
 -----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<grid>>

=============================================================================