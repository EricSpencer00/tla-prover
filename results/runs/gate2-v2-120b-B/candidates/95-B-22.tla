----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N

VARIABLE grid

(* Ensure N is a natural number *)
ASSUME N \in Nat

vars == <<grid>>

(* Recursive function to sum a numeric function over a finite set *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* All valid positions on the board *)
Pos == { <<x, y>> : x \in 1..N, y \in 1..N }

(* Type invariant: grid maps each position to a Boolean value *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that assigns a score of 1 to live cells and 0 to dead or out‑of‑bounds cells *)
sc[<<x, y>> \in (0 .. N+1) \X (0 .. N+1)] ==
  IF (x = 0) \/ (y = 0) \/ (x > N) \/ (y > N) \/ ~grid[<<x, y>>]
     THEN 0
     ELSE 1

(* Number of live neighbours of position p *)
score(p) ==
  LET nbrs  == { <<dx, dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1}, <<dx, dy>> # <<0, 0>> }
      points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
  IN Sum(sc, points)

(* Initial state: any Boolean mapping of the board is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Evolution rule: standard Game‑of‑Life update *)
Next == grid' = [p \in Pos |-> 
                  IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
                     THEN TRUE
                     ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================