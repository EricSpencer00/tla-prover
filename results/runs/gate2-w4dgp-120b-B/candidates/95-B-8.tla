----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat

VARIABLE grid
vars == grid

Pos == {<<x, y>> : x, y \in 1..N}

\* Sum of a function over a finite domain.
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE x \in S : TRUE
                   IN f[x] + Sum(f, S \ {x})

\* Score of a cell is computed from a fixed neighborhood extended by one beyond
\* the board.  The kernel is defined on the super-domain (0..N+1)^2 and the
\* off-board points are handled by sc as a conditional definition.
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] ==
  CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N \/ ~grid[<<x, y>>]
       -> 0
       [] OTHER -> 1

score(p) ==
  LET nbrs == {<<dx, dy>> \in {-1, 0, 1} \X {-1, 0, 1} : <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

\* Init is unrestricted (any layout is possible); the safety property below is
\* what keeps every reachable state well-typed, not the initializer.
Init == grid \in [Pos -> BOOLEAN]

\* Conway's Life rule applied to the bounded board.
Next == grid' = [p \in Pos |->
                  IF \/ (grid[p] /\ score(p) \in {2, 3})
                       \/ (~grid[p] /\ score(p) = 3)
                  THEN TRUE ELSE FALSE]

Spec == Init /\ [][Next]_vars

\* Every reachable state is a total function on Pos: no key is dropped or added.
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================