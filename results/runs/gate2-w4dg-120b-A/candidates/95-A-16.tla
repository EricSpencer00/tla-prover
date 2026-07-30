---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  N

Cells == (1 .. N) \X (1 .. N)

\* A cell is alive (= TRUE) or dead (= FALSE); all cells are initialized
\* nondeterministically, so any configuration is a possible start.
VARIABLES alive

vars == << alive >>

TypeOK ==
  /\ alive \in [Cells -> BOOLEAN]

Init ==
  /\ alive \in [Cells -> BOOLEAN]

\* Each cell counts its (admissible, in-bounds) live neighbors.  Cells outside
\* the grid are treated as dead (the IF guards below).
NeighborPositions(c) ==
  {p \in Cells :
     /\ p[1] >= c[1] - 1 /\ p[1] <= c[1] + 1
     /\ p[2] >= c[2] - 1 /\ p[2] <= c[2] + 1
     /\ p # c}

LiveNeighbors(c) ==
  Cardinality({p \in NeighborPositions(c) : alive[p]})

\* Fully deterministic simultaneous update: every cell advances together,
\* derived from the same current generation.
Tick ==
  /\ alive' = [c \in Cells |-> IF alive[c]
                 THEN LiveNeighbors(c) \in {2, 3}
                 ELSE LiveNeighbors(c) = 3]
  /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====