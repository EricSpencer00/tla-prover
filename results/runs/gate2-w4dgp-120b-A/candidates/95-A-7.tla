---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Cells: each grid position holds a cell that is alive or dead.
\* Grid: an N-by-N square; positions outside the grid are treated as dead.
\* The system evolves by deterministic, fully-synchronous updates (a "tick"):
\* every cell is recomputed from its neighbors in the same step.

Cells == 1..N
Positions == Cells \X Cells

VARIABLES alive

vars == <<alive>>

TypeOK == alive \in [Positions -> BOOLEAN]

\* Given a grid position, the set of positions of its (up to eight) neighbors,
\* restricted to those positions that fall inside the N-by-N grid.
Neighbors(p) == {q \in Positions : q # p /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1
                                /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1}

\* The number of live neighbors of position p; positions outside the grid are
\* simply absent from Neighbors(p), and therefore contribute zero.
LiveCount(p) == Cardinality({q \in Neighbors(p) : alive[q]})

Init == alive = [p \in Positions |-> CHOOSE b \in BOOLEAN : TRUE]

\* Tick: every cell updates simultaneously, driven by its neighbor count.
\* Live cells with 2 or 3 neighbors survive; dead cells with exactly 3 neighbors
\* become alive; all other cells die. Because this is a function of the current
\* grid alone, it is a deterministic bulk update -- no choice or race exists.
Tick ==
    /\ alive' = [p \in Positions |-> IF alive[p]
                    THEN LiveCount(p) = 2 \/ LiveCount(p) = 3
                    ELSE LiveCount(p) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

====