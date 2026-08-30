---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES grid

TypeOK == grid \in [1..N \times 1..N -> BOOLEAN]

Init == \E g \in [1..N \times 1..N -> BOOLEAN] : grid = g

\* Count live neighbors of cell (r, c), treating cells outside the
\* NxN grid as dead (zero value).
\* r/c range from 1 to N, so an out-of-bounds cell is not in the domain.
NeighborCount(r, c) ==
  Cardinality({p \in 1..N \times 1..N :
                 grid[p] /\ p # <<r, c>> /\ \E dr \in -1..1, dc \in -1..1 :
                   dr = p[1] - r /\ dc = p[2] - c})

Tick ==
  /\ \E nextGrid \in [1..N \times 1..N -> BOOLEAN] :
       \A p \in 1..N \times 1..N :
         LET cnt == NeighborCount(p[1], p[2]) IN
         nextGrid[p] =
           IF grid[p] THEN cnt = 2 \/ cnt = 3
           ELSE cnt = 3
  /\ grid' = nextGrid

Next == Tick

Spec == Init /\ [][Next]_grid

StateConstraint == TypeOK

====