------------------------------ MODULE GameOfLife ------------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* N is a natural number *)
ASSUME N \in Nat

(* Helper for recursive sum of a function f over a finite set S *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* Set of positions inside the NxN board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* grid must be a total function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Score contribution of a single cell (x,y) *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0
          \/ x > N \/ y > N
          \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* Number of alive neighbours of position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any assignment of TRUE/FALSE to every board cell *)
Init == grid \in [Pos -> BOOLEAN]

(* Transition: standard Game of Life rules *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Safety invariant that the state never violates the type definition *)
TypeOKInv == grid \in [Pos -> BOOLEAN]

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

=============================================================================