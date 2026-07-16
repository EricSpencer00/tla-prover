----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers, Naturals

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

Pos == {<<x, y>> : x \in 1..N, y \in 1..N}
TypeOK == grid \in [Pos -> BOOLEAN]

RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* The scoring function uses only positions that are guaranteed to be
   within Pos, therefore it never accesses grid outside its domain. *)
sc[p \in Pos] ==
  IF grid[p] THEN 0 ELSE 1

score(p) ==
  LET nbrs == {<<dx, dy>> : dx \in {-1, 0, 1}, dy \in {-1, 0, 1},
                <<dx, dy>> # <<0, 0>>}
      points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in nbrs}
  IN Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
  grid' = [p \in Pos |-> 
            IF (grid[p] /\ score(p) \in {2,3}) \/
               (~grid[p] /\ score(p) = 3)
            THEN TRUE
            ELSE FALSE]

Spec == Init /\ [][Next]_grid

====