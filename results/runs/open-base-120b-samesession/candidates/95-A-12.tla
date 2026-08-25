---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

(*-----------------------------------------------------------------
  Definition of the set of positions on the N-by-N grid.
-----------------------------------------------------------------*)
Pos == 1 .. N \X 1 .. N

(*-----------------------------------------------------------------
  Absolute value function needed for neighbor calculations.
-----------------------------------------------------------------*)
Abs(x) == IF x < 0 THEN -x ELSE x

(*-----------------------------------------------------------------
  Predicate indicating that q is a neighbor of p (including diagonals).
  Positions outside the grid are simply not members of Pos, so they are
  ignored in neighbor counting.
-----------------------------------------------------------------*)
IsNeighbor(p, q) ==
    /\ p # q
    /\ Abs(p[1] - q[1]) <= 1
    /\ Abs(p[2] - q[2]) <= 1

(*-----------------------------------------------------------------
  Type invariant: grid maps every position to a Boolean value.
-----------------------------------------------------------------*)
TypeOK == grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state: any assignment of Booleans to the grid is allowed.
-----------------------------------------------------------------*)
Init == grid \in [Pos -> BOOLEAN]

(*-----------------------------------------------------------------
  The simultaneous update rule (Tick).  For each position p we
  compute the number of live neighbors n and set grid'[p] according
  to the Game of Life rules.
-----------------------------------------------------------------*)
Next ==
    \A p \in Pos :
        LET n == Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] }) IN
        grid'[p] = ( (grid[p] /\ (n = 2 \/ n = 3)) \/ (~grid[p] /\ n = 3) )

(*-----------------------------------------------------------------
  Specification: start in Init and forever take steps satisfying Next.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_grid

====