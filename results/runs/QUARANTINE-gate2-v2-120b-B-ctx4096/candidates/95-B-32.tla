----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* ------------------------------------------------------------------------ *)
(* Recursive sum over a finite set of positions.  The function f is expected
   to return a natural number for any point in its domain, which is ensured
   by the definitions below. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* The set of all positions inside the N-by-N board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------------ *)
(* TypeOK was intended to express that grid is a total function from Pos to
   BOOLEAN, but the original definition used \notin, which made the invariant
   false for every state (including the initial one).  The corrected invariant
   asserts the intended type condition directly. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------------ *)
(* The neighbourhood of a cell consists of the eight surrounding cells. *)
nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

(* Count the number of living neighbours of a position p. *)
LiveNeighbors(p) ==
  Cardinality({q \in Pos :
                <<p[1] + q[1], p[2] + q[2]>> \in Pos /\ grid[<<p[1] + q[1], p[2] + q[2]>>]})

(* The score function used in the original specification can be expressed
   directly as the number of live neighbours. *)
score(p) == LiveNeighbors(p)

(* ------------------------------------------------------------------------ *)
(* Initial state: any assignment of TRUE/FALSE to every cell is allowed. *)
Init == grid \in [Pos -> BOOLEAN]

(* Next-state relation implements the standard Game of Life rules. *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ score(p) \in {2, 3})
           \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================