---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Each cell is either alive (TRUE) or dead (FALSE).  The state is the mapping
\* from grid position to that boolean value.
VARIABLES alive

vars == <<alive>>

Positions == (1..N) \X (1 .. N)

\* The number of live neighbors a cell has.  Positions outside the N-by-N grid
\* are treated as dead (value FALSE) by the definition of Neighbor.
NumLiveNeighbors(p) ==
  LET nbs == [dx \in -1..1, dy \in -1..1 |-> <<p[1] + dx, p[2] + dy>>]
  IN Cardinality({k \in 1..8 : LET q == nbs[CHOOSE i \in 1..8 : TRUE] : q \in Positions /\ alive[q]})

\* A live cell survives with exactly 2 or 3 live neighbors.  A dead cell is
\* born with exactly 3 live neighbors.
Survives(p) == alive[p] /\ NumLiveNeighbors(p) \in {2, 3}
Born(p) == ~alive[p] /\ NumLiveNeighbors(p) = 3

TypeOK ==
  /\ alive \in [Positions -> BOOLEAN]

Init ==
  /\ alive \in [Positions -> BOOLEAN]

Next ==
  /\ alive' = [p \in Positions |-> Survives(p) \/ Born(p)]

Spec ==
  /\ Init
  /\ [][Next]_vars

====