----
MODULE GameOfLife
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

\* ---------- Helper definitions ----------
Pos == {<<x, y>> : x, y \in 1..N}
Nbrs == {<<dx, dy>> : dx, dy \in {-1, 0, 1} /\ <<dx, dy>> # <<0, 0>>}

\* Count the number of live neighbours of a cell p.
NeighbourCount(p) ==
  LET points == {<<p[1] + dx, p[2] + dy>> : <<dx, dy>> \in Nbrs}
  IN
    \A q \in points : q \in Pos => IF grid[q] THEN 1 ELSE 0

\* ---------- Specification ----------
Init == /\ grid \in [Pos -> BOOLEAN]
        /\ \A p \in Pos : grid[p] = FALSE   \* all cells start dead

Next ==
  /\ grid' = [p \in Pos |-> 
        IF \/ (grid[p] /\ (NeighbourCount(p) \in {2,3}))
           \/ (~grid[p] /\ (NeighbourCount(p) = 3))
        THEN TRUE
        ELSE FALSE]

Spec == Init /\ [][Next]_vars

\* ---------- Invariant ----------
TypeOK == grid \in [Pos -> BOOLEAN]

====