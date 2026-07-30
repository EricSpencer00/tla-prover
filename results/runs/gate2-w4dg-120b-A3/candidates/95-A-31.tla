---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Each grid position holds a cell; the value is TRUE iff the cell is alive.
VARIABLES cell

vars == <<cell>>

Positions == {p \in (1..N) \X (1..N) : TRUE}

Outside == (0..(N + 1)) \X (0..(N + 1))

\* A neighbor may lie outside the grid; those positions are treated as dead.
Canonical(p) == IF p \in Positions THEN p ELSE <<0, 0>>

Neighbors(p) == {q \in (Positions \cup Outside) :
                      p # q /\ ABS(p[1] - q[1]) <= 1 /\ ABS(p[2] - q[2]) <= 1}

TypeOK == cell \in [Positions -> BOOLEAN]

\* Every cell is updated, simultaneously, from the current generation.
\* The update is deterministic given the current grid state.
Tick ==
  /\ cell' = [p \in Positions |-> LET
                liveCount == Cardinality({q \in Neighbors(p) : cell[Canonical(q)]})
                current == cell[p]
              IN IF current
                   THEN liveCount = 2 \/ liveCount = 3
                   ELSE liveCount = 3]

Init ==
  /\ cell \in [Positions -> BOOLEAN]

Spec == Init /\ [][Tick]_vars

====