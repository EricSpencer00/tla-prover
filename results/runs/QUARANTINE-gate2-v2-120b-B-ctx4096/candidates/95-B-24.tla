---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive definition of Sum, unchanged *)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

(* Set of all positions on the board *)
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

(* Corrected type invariant: grid must be a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Score function, unchanged *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0
       \/ x > N \/ y > N
       \/ ~grid[<<x, y>>] -> 0
  [] OTHER -> 1

score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial predicate unchanged; it already ensures grid is a function over Pos *)
Init == grid \in [Pos -> BOOLEAN]

(* Next-state relation unchanged *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

====