---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

Pos == {<<x, y>> : x, y \in 1..N}

(* Sum of the integer values of a function f over a finite set S *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Type invariant: the grid must be a total function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper to compute the contribution of a neighbour cell to the score *)
sc(p) ==
  LET x == p[1] , y == p[2] IN
    IF 1 <= x /\ x <= N /\ 1 <= y /\ y <= N THEN
      IF grid[p] THEN 1 ELSE 0
    ELSE 0

(* Number of live neighbours of position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>} IN
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs} IN
  Sum(sc, points)

(* Initial state: any mapping from Pos to BOOLEAN is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Standard Game of Life update rule *)
Next ==
  /\ grid' = [p \in Pos |-> 
                IF (grid[p] /\ score(p) \in {2, 3}) \/
                   (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

====