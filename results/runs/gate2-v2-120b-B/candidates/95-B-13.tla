------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers, Sequences

CONSTANT N
VARIABLE grid

(* The grid is a mapping from positions (x,y) with 1 <= x,y <= N to BOOLEAN.
   This captures the set of alive (TRUE) or dead (FALSE) cells. *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Recursive sum over a finite set of positions. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Helper that determines whether a neighbor position is inside the board. *)
InBoard(p) == /\ p[1] \in 1..N
              /\ p[2] \in 1..N

(* Scoring function: counts how many alive neighbors a position has. *)
sc(p) ==
  LET nbrs == {<<dx, dy>> : dx \in -1..1, dy \in -1..1, <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Cardinality({q \in points : InBoard(q) /\ grid[q]})

(* Initialization: any assignment of TRUE/FALSE to every cell is allowed,
   provided the type invariant holds. *)
Init == grid \in [Pos -> BOOLEAN]

(* Next-state relation implements the standard Game of Life rules. *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ sc(p) \in {2, 3}) \/ (~grid[p] /\ sc(p) = 3)
        THEN TRUE
        ELSE FALSE]
  /\ TypeOK

(* Full specification. *)
Spec == Init /\ [][Next]_<<grid>>

=============================================================================