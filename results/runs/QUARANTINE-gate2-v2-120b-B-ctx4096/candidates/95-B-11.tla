----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

\* Ensure N is a non‑negative integer (a natural number)
ASSUME N \in Nat

vars == <<grid>>

\* Recursive sum over a finite set of positions
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* The set of valid positions inside the N×N board
Pos == {<<x, y>> : x \in 1..N, y \in 1..N}

\* Type invariant: each position maps to a Boolean value (alive or dead)
TypeOK == grid \in [Pos -> BOOLEAN]

\* Helper that counts live neighbours for a given position p
score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in -1..1, dy \in -1..1, <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs,
                 p[1] + dx \in 1..N, p[2] + dy \in 1..N}
  IN Sum(grid, points)

\* Initial state: any assignment of Boolean values to all positions
Init == grid \in [Pos -> BOOLEAN]

\* Classical Game‑of‑Life update rule
Next ==
  /\ grid' = [p \in Pos |-> 
        IF (grid[p] /\ score(p) \in {2, 3}) \/
           (~grid[p] /\ score(p) = 3)
        THEN TRUE
        ELSE FALSE]

Spec == Init /\ [][Next]_vars

=============================================================================