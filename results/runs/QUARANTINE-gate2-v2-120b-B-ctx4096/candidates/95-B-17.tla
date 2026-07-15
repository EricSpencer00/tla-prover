----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* N is a natural number *)
ASSUME N \in Nat

vars == grid

(* Recursive definition of Sum over a finite set S of positions. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* The set of valid positions on the N x N board. *)
Pos == { <<x, y>> : x, y \in 1..N }

(* Type invariant: grid must be a function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that counts a live neighbor as 1, dead or out‑of‑bounds as 0. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE
    \/ x = 0 \/ y = 0 \/ x > N \/ y > N -> 0
    [] grid[<<x, y>>] -> 1
    [] OTHER -> 0

(* Number of live neighbors of position p. *)
score(p) ==
  LET nbrs  == { <<dx, dy>> \in {-1,0,1} \X {-1,0,1} : <<dx, dy>> # <<0,0>> }
      points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
  IN Sum(sc, points)

(* Initialization: any assignment of BOOLEAN values to the board is allowed. *)
Init == grid \in [Pos -> BOOLEAN]

(* Evolution rule: standard Game of Life update based on neighbor count. *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2,3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================