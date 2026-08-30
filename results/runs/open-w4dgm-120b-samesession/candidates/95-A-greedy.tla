---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == (1..N) \X (1..N)

\* A cell outside the grid is treated as dead for neighbor-counting.
Alive(p) == IF p \in Cells THEN grid[p] ELSE FALSE

Neighbors(p) ==
  { q \in Cells :
      q # p /\ (q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1)
               /\ (q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1) }

LiveCount(p) == Cardinality({ q \in Neighbors(p) : Alive(q) })

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
  \E g \in [Cells -> BOOLEAN] : grid = g

\* Fully deterministic simultaneous update: the next generation is uniquely
\* determined by the current one, so the model is deterministic after Init.
Tick ==
  grid' = [p \in Cells |-> IF grid[p] /\ (LiveCount(p) = 2 \/ LiveCount(p) = 3)
                          THEN TRUE
                          ELSE IF ~grid[p] /\ LiveCount(p) = 3
                          THEN TRUE
                          ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====