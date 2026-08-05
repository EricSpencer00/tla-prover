---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Conway's Game of Life on a fixed N-by-N grid with hard boundaries.
\* Cells outside the grid are dead when counting neighbors.

Idx == 1..N
Positions == [r: Idx, c: Idx]

VARIABLES alive

\* Count live neighbors of a position, using zero for positions outside the grid.
Neighbors(pos) == {
  p \in Positions :
    p.r \in {pos.r - 1, pos.r, pos.r + 1} /\ p.c \in {pos.c - 1, pos.c, pos.c + 1} /\ (p.r # pos.r \/ p.c # pos.c)
}

LiveNeighbors(pos) == Cardinality({p \in Neighbors(pos) : alive[p]})

TypeOK == alive \in [Positions -> BOOLEAN]

Init ==
  /\ alive \in [Positions -> BOOLEAN]

\* Every cell updates simultaneously based on the same original generation.
Tick ==
  /\ \E na \in [Positions -> BOOLEAN] :
       /\ \A pos \in Positions :
            na[pos] =
              \/ (alive[pos] /\ LiveNeighbors(pos) \in 2..3)
              \/ (~alive[pos] /\ LiveNeighbors(pos) = 3)
       /\ alive' = na

Next == Tick

Spec == Init /\ [][Next]_alive

====