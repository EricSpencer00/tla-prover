---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* A grid position is given by a row and column index, each from 1..N.
Positions == [r \in 1..N, c \in 1..N]

VARIABLES cells

vars == <<cells>>

\* Count the live orthogonal and diagonal neighbors of position p, treating
\* every position outside the grid as dead (value zero).
NeighborCount(p) ==
  LET nbrs == {{q.r, q.c} : q \in [r \in {p.r - 1, p.r, p.r + 1}, c \in {p.c - 1, p.c, p.c + 1}] : (q.r # p.r \/ q.c # p.c) /\ (q.r \in 1..N /\ q.c \in 1..N)}
  IN  Cardinality({q \in nbrs : cells[q]})

Init ==
  \* Nondeterministically assign each cell alive or dead; every configuration
  \* of the grid is a possible initial state.
  \E f \in [Positions -> BOOLEAN] : cells = f

Tick ==
  \* Simultaneous update: each cell is recomputed from its current neighbor
  \* count. Cells outside the grid are dead and are never in the domain of cells.
  /\ \E f \in [Positions -> BOOLEAN] :
       \A p \in Positions :
         f[p] = Iff(cells[p], NeighborCount(p) \in {2, 3}, NeighborCount(p) = 3)
  /\ cells' = f

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ cells \in [Positions -> BOOLEAN]
  /\ N \in Nat /\ N >= 1

====