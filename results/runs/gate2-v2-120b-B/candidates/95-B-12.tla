---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* ------------------------------------------------------------------------- *)
(* Helper definitions *)
(* ------------------------------------------------------------------------- *)

(* The set of positions that are part of the board. *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------------- *)
(* Recursive sum over a finite set of points, using a function f that maps *)
(* each point to an integer.                                                  *)
(* ------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------------- *)
(* Score function: counts the number of live neighbours of a point p.        *)
(* The function sc is defined only for points that lie in the extended grid *)
(* (including a one‑cell border).                                            *)
(* ------------------------------------------------------------------------- *)

(* The extended domain, used by sc.                                         *)
ExtPos == (0 .. N+1) \X (0 .. N+1)

(* sc[p] = 0 if p is outside the board or the cell is dead;                *)
(*        = 1 otherwise.                                                    *)
sc[p \in ExtPos] ==
  IF \/ p[1] = 0 \/ p[2] = 0
        \/ p[1] > N \/ p[2] > N
        \/ ~grid[p] THEN 0
  ELSE 1

(* The set of the eight neighbour offsets.                                   *)
NbrOffsets == {<<dx, dy>> \in {-1,0,1} \X {-1,0,1} : <<dx, dy>> # <<0,0>>}

(* The eight neighbour positions of p.                                       *)
Neighbours(p) == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in NbrOffsets}

(* The number of live neighbours of p.                                       *)
score(p) == Sum(sc, Neighbours(p))

(* ------------------------------------------------------------------------- *)
(* Initialization and transition actions                                    *)
(* ------------------------------------------------------------------------- *)

(* The grid is any mapping from the board positions to Boolean values.       *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life update rule.                                                 *)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ score(p) \in {2,3})
           \/ (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)

vars == <<grid>>
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type invariant: the variable must always be a function from board        *)
(* positions to Boolean values.                                              *)
(* ------------------------------------------------------------------------- *)

TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================