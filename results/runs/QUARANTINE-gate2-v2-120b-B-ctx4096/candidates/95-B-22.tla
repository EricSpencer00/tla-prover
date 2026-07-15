---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* ------------------------------------------------------------------- *)
(* The set of all positions on the NxN board                             *)
Pos == {<<x, y>> : x, y \in 1..N}

(* ------------------------------------------------------------------- *)
(* Recursive definition of the sum of a function over a finite set.     *)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------- *)
(* Type predicate: grid must be a total function from Pos to BOOLEAN.   *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------- *)
(* Helper that returns 1 for a live cell and 0 for a dead (or out of     *)
   bounds) cell.                                                       *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] == 
    IF \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] 
       THEN 0 
       ELSE 1

(* ------------------------------------------------------------------- *)
(* Number of live neighbours of position p.                             *)
score(p) == 
    LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
        points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
    IN Sum(sc, points)

(* ------------------------------------------------------------------- *)
(* Initial state: any assignment of live/dead to every board cell.      *)
Init == grid \in [Pos -> BOOLEAN]

(* ------------------------------------------------------------------- *)
(* Standard Game of Life transition rule.                               *)
Next == 
    grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ score(p) \in {2, 3})
           \/ (~grid[p] /\ score(p) = 3)
           THEN TRUE
           ELSE FALSE]

(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_grid

====