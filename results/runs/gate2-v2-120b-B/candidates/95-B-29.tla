---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

(* Recursive sum over a finite set of positions *)
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

(* All valid positions on the grid *)
Pos == {<<i, j>> : i, j \in 1..N}

(* The intended type invariant: grid must be a function from positions to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper function: returns 0 for out‑of‑bounds positions, otherwise 1 if the cell is alive *)
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N
          \/ ~grid[<<x, y>>] -> 0
       [] OTHER -> 1

(* Number of alive neighbours of position p, using Sum over the eight surrounding cells *)
score(p) ==
  LET nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

(* Initial state: any assignment of FALSE/TRUE to every position satisfies the type invariant *)
Init == grid \in [Pos -> BOOLEAN]

(* Game of Life transition rule *)
Next ==
  grid' = [p \in Pos |-> IF \/ (grid[p] /\ score(p) \in {2, 3})
                            \/ (~grid[p] /\ score(p) = 3)
                         THEN TRUE
                         ELSE FALSE]

Spec == Init /\ [][Next]_vars

====