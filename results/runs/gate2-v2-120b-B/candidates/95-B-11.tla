---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE grid

(* The board positions, each represented as a tuple <<x, y>> *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* The initial state must assign a Boolean value to every position. *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

(* Recursive sum over a finite set S of points, applying function f to each. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN
       f[x] + Sum(f, S \ {x})

(* For a point p, the 8 neighboring coordinates (including possible off‑board
   points). *)
nbrs == {<<dx, dy>> : dx \in -1..1, dy \in -1..1, ~(dx = 0 /\ dy = 0)}

(* Number of live (TRUE) neighbors of p, counting only those that lie inside
   the board. *)
LiveNeighbors(p) ==
  Cardinality({ q \in Pos :
                 <<p[1] + q[1], p[2] + q[2]>> \in Pos /\ grid[<<p[1] + q[1], p[2] + q[2]>>]})

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------- *)

Next ==
  grid' = [p \in Pos |-> 
            IF grid[p] /\ LiveNeighbors(p) \in {2, 3}
               THEN TRUE
               ELSE IF ~grid[p] /\ LiveNeighbors(p) = 3
                       THEN TRUE
                       ELSE FALSE]

vars == <<grid>>

Spec == Init /\ [][Next]_vars

=============================================================================