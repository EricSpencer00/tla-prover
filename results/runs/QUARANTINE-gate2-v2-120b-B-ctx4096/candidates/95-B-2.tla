---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

Pos == {<<x, y>> : x, y \in 1..N}

(* -------------------------------------------------------------------------- *)
(* The original invariant `TypeOK` was incorrectly defined as a *negated*   *)
(* type test, causing every initial state to violate it.  The corrected      *)
(* version asserts that `grid` *is* a function from positions to Boolean    *)
(* values, which matches the intended model of a finite Game of Life board.*)
(* -------------------------------------------------------------------------- *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* -------------------------------------------------------------------------- *)
(* Recursive sum over a finite set of positions using a function that maps    *)
(* each position to a natural number.                                         *)
(* -------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* -------------------------------------------------------------------------- *)
(* Score of a cell: number of live neighbours.  The auxiliary function `sc`  *)
(* returns 1 for a live cell inside the grid and 0 otherwise.                 *)
(* -------------------------------------------------------------------------- *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N THEN 0
       [] grid[<<x, y>>] = FALSE THEN 0
       [] OTHER THEN 1

score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* -------------------------------------------------------------------------- *)
(* Initialization: any assignment of Boolean values to every position is    *)
(* allowed.                                                                   *)
(* -------------------------------------------------------------------------- *)
Init == grid \in [Pos -> BOOLEAN]

(* -------------------------------------------------------------------------- *)
(* Transition relation implementing the standard Game of Life rules.        *)
(* -------------------------------------------------------------------------- *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

vars == <<grid>>

Spec == Init /\ [][Next]_vars

====