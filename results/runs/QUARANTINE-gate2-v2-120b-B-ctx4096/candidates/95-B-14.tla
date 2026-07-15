---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

(* The constant N must be a natural number. *)
ASSUME N \in Nat

(* Alias for the set of variables, used in the temporal operator. *)
vars == grid

(* Recursive definition of a sum over a finite set of points, applying a function f. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* The set of valid positions on the NxN board. *)
Pos == { <<x, y>> : x, y \in 1..N }

(* The type invariant: grid must be a total function from Pos to BOOLEAN. *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that returns 0 for out‑of‑bounds or dead cells,
   and 1 for live cells that are inside the board. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0
         \/ x > N \/ y > N
         \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* The score of a cell is the number of live neighbours. *)
score(p) ==
  LET nbrs == { <<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>> }
      points == { <<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs }
  IN Sum(sc, points)

(* Initial state: any assignment of TRUE/FALSE to every board position. *)
Init == grid \in [Pos -> BOOLEAN]

(* Evolution rule: the classic Game‑of‑Life update. *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

(* Full specification: start in Init and repeatedly apply Next. *)
Spec == Init /\ [][Next]_vars

=============================================================================