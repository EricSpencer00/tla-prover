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

(* Set of all valid positions on the board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function that assigns a score contribution to a position:
   0 for out‑of‑bounds or dead cells, 1 otherwise. *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* Number of live neighbours of position p *)
score(p) ==
  LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
      points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any assignment of dead/alive to every position *)
Init == grid \in [Pos -> BOOLEAN]

(* Game‑of‑Life transition *)
Next ==
  grid' = [p \in Pos |-> 
            IF \/ (grid[p] /\ score(p) \in {2, 3})
               \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================