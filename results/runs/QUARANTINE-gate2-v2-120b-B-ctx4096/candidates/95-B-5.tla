----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

Pos == {<<x, y>> : x, y \in 1..N}

(* Invariant states that each entry of the grid is either TRUE or FALSE.
   This correctly captures the intended typing of the grid. *)
TypeOK == grid \in [Pos -> BOOLEAN]

RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN  f[x] + Sum(f, S \ {x})

(* Neighborhood points (including the cell itself). *)
neighPoints(p) ==
  {<<p[1] + i, p[2] + j>> :
      i \in -1..1 /\ j \in -1..1}

(* Number of live cells among the eight neighbors of p, excluding p. *)
liveNbrs(p) ==
  Cardinality({q \in neighPoints(p) :
                 q # p /\ q \in Pos /\ grid[q]})

(* Standard Game of Life rule. *)
Next ==
  /\ grid' \in [Pos -> BOOLEAN]
  /\ \A p \in Pos :
        grid'[p] =
          IF \/ (grid[p] /\ liveNbrs(p) \in {2,3})
             \/ (~grid[p] /\ liveNbrs(p) = 3)
          THEN TRUE
          ELSE FALSE

Init == grid \in [Pos -> BOOLEAN]

Spec == Init /\ [][Next]_vars

=============================================================================