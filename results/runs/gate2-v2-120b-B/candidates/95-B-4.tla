----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* All valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Correct type invariant: grid maps each position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Score contribution of a single cell: 1 for a live neighbor, 0 otherwise *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  IF \/ x = 0 \/ y = 0 \/ x > N \/ y > N
        \/ ~grid[<<x, y>>]
     THEN 0
     ELSE 1

(* Total number of live neighbors of position p *)
score(p) ==
  LET nbrs  == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any Boolean assignment to the board *)
Init == grid \in [Pos -> BOOLEAN]

(* Transition: apply the Game of Life rules to every cell *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================