---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

(*-----------------------------------------------------------------
  The set of positions on the N-by-N grid.
-----------------------------------------------------------------*)
Pos == 1..N \X 1..N

(*-----------------------------------------------------------------
  Helper function: absolute difference between two natural numbers.
-----------------------------------------------------------------*)
Dist(i, j) == IF i >= j THEN i - j ELSE j - i

(*-----------------------------------------------------------------
  Two positions are adjacent (including diagonally) and distinct.
-----------------------------------------------------------------*)
Adjacent(p, q) ==
  /\ p # q
  /\ Dist(p[1], q[1]) <= 1
  /\ Dist(p[2], q[2]) <= 1

(*-----------------------------------------------------------------
  Number of live neighbours of position p in the current grid.
  Positions outside the grid are ignored (treated as dead).
-----------------------------------------------------------------*)
LiveNeighbors(p) ==
  Cardinality({ q \in Pos : Adjacent(p, q) /\ grid[q] })

(*-----------------------------------------------------------------
  State predicate stating that all variables have correct types.
-----------------------------------------------------------------*)
TypeOK ==
  /\ grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state: each cell may be alive or dead arbitrarily.
-----------------------------------------------------------------*)
Init ==
  /\ grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
  The simultaneous update of the whole grid (the "Tick").
-----------------------------------------------------------------*)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF grid[p] THEN (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
        ELSE LiveNeighbors(p) = 3]

(*-----------------------------------------------------------------
  Specification of the system.
-----------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<grid>>

=============================================================================