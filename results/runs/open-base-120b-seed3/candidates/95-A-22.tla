---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(*-----------------------------------------------------------------
  The set of all positions on the N×N grid.
-----------------------------------------------------------------*)
CellPos == 1..N X 1..N

(*-----------------------------------------------------------------
  Type invariant: each position maps to a Boolean (TRUE = alive,
  FALSE = dead).
-----------------------------------------------------------------*)
TypeOK == grid \in [CellPos -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state: any Boolean assignment to the grid positions.
-----------------------------------------------------------------*)
Init == grid \in [CellPos -> BOOLEAN]

(*-----------------------------------------------------------------
  Two distinct positions are neighbors if they differ by at most 1
  in each coordinate (including diagonals).
-----------------------------------------------------------------*)
IsNeighbor(p, q) ==
  /\ p # q
  /\ Abs(p[1] - q[1]) <= 1
  /\ Abs(p[2] - q[2]) <= 1

(*-----------------------------------------------------------------
  Number of live neighbors of position p in the current grid.
-----------------------------------------------------------------*)
NeighborCount(p) ==
  Cardinality({ q \in CellPos : IsNeighbor(p, q) /\ grid[q] })

(*-----------------------------------------------------------------
  Simultaneous update of all cells according to the Game of Life rules.
-----------------------------------------------------------------*)
Next ==
  LET cnt == [p \in CellPos |-> NeighborCount(p)] IN
    /\ grid' = [p \in CellPos |
          IF  grid[p] /\ (cnt[p] = 2 \/ cnt[p] = 3) THEN TRUE
          ELSE IF ~grid[p] /\ cnt[p] = 3 THEN TRUE
          ELSE FALSE]

(*-----------------------------------------------------------------
  The full specification: start in Init and forever apply Next.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<grid>>

====