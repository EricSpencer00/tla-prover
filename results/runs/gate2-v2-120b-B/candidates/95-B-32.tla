----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N

VARIABLE grid

(* The constant N is required to be a natural number *)
ASSUME N \in Nat

vars == grid

(* Recursive definition of a sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* The set of all valid positions on the N×N board *)
Pos == {<<x, y>> : x, y \in 1..N}

(* Type invariant: grid must be a total function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper predicate that yields 1 for a live cell inside the board,
   and 0 otherwise (including out‑of‑bounds cells) *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N
         -> 0
       [] grid[<<x, y>>] = TRUE
         -> 1
       [] OTHER
         -> 0

(* Compute the number of live neighbours of a position p *)
score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any assignment of Boolean values to the board is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* Next-state relation implements the Game of Life rules *)
Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2, 3}) \/ (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================