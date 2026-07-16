----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

(* The set of positions inside the N×N board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* A helper that computes the sum of a function over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN  f[x] + Sum(f, S \ {x})

(* The invariant that ensures the variable stays within the intended domain *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* The score contributed by a position (including a border of dead cells) *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* The total number of alive neighbours around a position p *)
score(p) ==
  LET nbrs == { <<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>> }
      points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
  IN  Sum(sc, points)

(* Initial state: any assignment of dead/alive to the board positions *)
Init == grid \in [Pos -> BOOLEAN]

(* Transition relation: standard Game of Life rules applied to each cell *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
               THEN TRUE
               ELSE FALSE]

Spec == Init /\ [][Next]_<<grid>>

=============================================================================