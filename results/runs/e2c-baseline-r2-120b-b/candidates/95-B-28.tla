---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

Pos == {<<x, y>> : x, y \in 1..N}
TypeOK == grid \in [Pos -> BOOLEAN]

(* contribution of a cell to the neighbour count; 1 if the cell is alive,
   0 otherwise (including cells outside the board) *)
sc(p) == IF p \in Pos THEN IF grid[p] THEN 1 ELSE 0 ELSE 0

score(p) ==
    LET nbrs == {<<x, y>> \in {-1, 0, 1} \X {-1, 0, 1} : <<x, y>> # <<0, 0>>}
        points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
    IN  Sum(sc, points)

Init == grid \in [Pos -> BOOLEAN]

Next ==
    grid' = [p \in Pos |
                IF (grid[p] /\ score(p) \in {2, 3}) \/
                   (~grid[p] /\ score(p) = 3)
                THEN TRUE
                ELSE FALSE]

Spec == Init /\ [][Next]_vars

====