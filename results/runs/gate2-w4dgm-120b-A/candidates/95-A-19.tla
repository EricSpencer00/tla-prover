---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells

\* cells[p] = TRUE means the cell at grid position p = <<i, j>> is alive; FALSE means dead.
vars == <<cells>>

Positions == 1..N
GridPos == Positions \X Positions

\* All positions inside the N-by-N grid; positions outside are treated as dead.
Inside(p) == p \in GridPos

LiveNeighbors(p) == Cardinality({q \in GridPos :
    q # p /\ Inside(q) /\ cells[q]
    /\ (q[1] - p[1]) \in {-1, 0, 1}
    /\ (q[2] - p[2]) \in {-1, 0, 1}})

TypeOK ==
    /\ cells \in [GridPos -> BOOLEAN]

Init ==
    /\ cells \in [GridPos -> BOOLEAN]

\* Fully synchronous update: every cell on the grid is recomputed from the
\* same, current generation of neighbor counts.
Tick ==
    /\ cells' = [p \in GridPos |-> IF cells[p] /\ LiveNeighbors(p) \in {2, 3}
                                      THEN TRUE
                                      ELSE IF ~ cells[p] /\ LiveNeighbors(p) = 3
                                      THEN TRUE
                                      ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====