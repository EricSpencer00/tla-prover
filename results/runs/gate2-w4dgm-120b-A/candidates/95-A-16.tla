---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A cell's position on the grid: row and column indices ranging from 1..N.
Positions == (1..N) \X (1..N)

\* A grid is a total function giving, for every valid position, whether that
\* cell is alive (TRUE) or dead (FALSE).
VARIABLES grid
vars == <<grid>>

TypeOK == grid \in [Positions -> BOOLEAN]

Init == \E g \in [Positions -> BOOLEAN] : grid = g

\* Count the live (TRUE) cells among a cell's neighboring positions. A
\* neighbor outside the grid is treated as dead, i.e. contributes zero.
NeighborCount(o) ==
  Cardinality({p \in Positions :
                 [x |-> p[1], y |-> p[2]] # o
                   /\ p[1] \in (o[1] - 1)..(o[1] + 1)
                   /\ p[2] \in (o[2] - 1)..(o[2] + 1)
                   /\ grid[p]})

\* The deterministic "tick": every cell simultaneously adopts its next state
\* derived from its own live-neighbor count.
Tick ==
  /\ grid' = [o \in Positions |-> IF grid[o] /\ (NeighborCount(o) \in {2, 3})
                                  THEN TRUE
                                  ELSIF ~grid[o] /\ (NeighborCount(o) = 3)
                                  THEN TRUE
                                  ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

\* Every reachable state assigns each position a boolean, so the reachable
\* state space stays within the shape assumed by TypeOK.
StateConstraint == TypeOK
====