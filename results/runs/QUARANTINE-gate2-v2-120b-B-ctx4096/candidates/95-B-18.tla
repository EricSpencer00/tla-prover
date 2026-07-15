---- MODULE GameOfLife ----
EXTENDS Integers, Naturals

CONSTANT N
VARIABLE grid

(* N must be a natural number *)
ASSUME N \in Nat

vars == <<grid>>

(* Recursive sum over a finite set S using function f *)
RECURSIVE Sum(_, _)
Sum(f, S) == 
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid maps each position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Scoring function for a neighbour *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] == 
  IF \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] 
     THEN 0 
     ELSE 1

(* Number of live neighbours of a position p *)
score(p) == 
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: every cell is initially dead *)
Init == grid = [p \in Pos |-> FALSE]

(* Game of Life transition *)
Next == 
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3}) 
               \/ (~grid[p] /\ score(p) = 3) 
               THEN TRUE 
               ELSE FALSE]

Spec == Init /\ [][Next]_vars

====