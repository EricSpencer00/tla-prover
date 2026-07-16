---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The set of positions that are inside the NxN board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

(* Sum over a finite set of positions using a function f *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE a \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* The eight neighbour offsets *)
NbrOffsets == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* ------------------------------------------------------------------------- *)
(* State predicate that the model checker expects                             *)
(* ------------------------------------------------------------------------- *)

vars == <<grid>>

Init == grid \in [Pos -> BOOLEAN]

(* The scoring function counts live neighbours.  It is defined only for
   positions inside Pos, which is sufficient for the subsequent Next action. *)
score(p) ==
    LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in NbrOffsets}
    IN Sum(
          [q \in points |-> IF q \in Pos /\ grid[q] THEN 1 ELSE 0],
          points
       )

Next ==
    /\ grid' = [p \in Pos |-> 
                 IF (grid[p] /\ score(p) \in {2, 3}) \/
                    (~grid[p] /\ score(p) = 3)
                 THEN TRUE
                 ELSE FALSE]

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Invariant: the grid always maps every board position to a Boolean value   *)
(* ------------------------------------------------------------------------- *)

TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================