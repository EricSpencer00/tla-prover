---- MODULE GameOfLife ----
\* Conway's Game of Life on a bounded square grid.  Each Tick updates the
\* whole grid at once, based on how many of the eight neighboring cells
\* around each position are alive (positions outside the grid are dead).
EXTENDS Naturals

CONSTANTS N

Positions == 1..N \X 1..N
Dead == 0
Live == 1

\* Alive[p] is the boolean cell value at position p; it is also used as a
\* numeric weight when counting live neighbors.
VARIABLES Alive

vars == <<Alive>>

TypeOK == Alive \in [Positions -> BOOLEAN]

Init == \E x \in [Positions -> BOOLEAN] : Alive = x

\* A cell outside the grid contributes nothing to its neighbor's count.
Weight(p) == IF p \in Positions THEN IF Alive[p] THEN Live ELSE Dead ELSE Dead

\* Count live neighbors for a cell at (r,c) by folding the weighting function
\* over the eight neighboring positions.
NeighborsAlive(r, c) ==
  LET deltas == {[-1..1, -1..1] \ {[0, 0]}} IN
    LET apply(d) ==
      LET p == <<r + d[1], c + d[2]>> IN Weight(p)
    IN LET sums == {apply(d) : d \in deltas} IN
         LET f[S \in SUBSET 1..8] ==
            IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE IN (apply(deltas[CHOOSE y \in S : TRUE])) + f[S \ {x}]
         IN f[1..8]

Tick ==
  \E nextAlive \in [Positions -> BOOLEAN] :
    /\ \A p \in Positions :
         /\ LET n == NeighborsAlive(p[1], p[2]) IN
            nextAlive[p] =
              (Alive[p] /\ (n = 2 \/ n = 3)) \/ (~Alive[p] /\ n = 3)
    /\ Alive' = nextAlive

Next == Tick

Spec == Init /\ [][Next]_vars

====