---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == <<cells>>

\* A Conway's Game of Life board, where the grid is a fixed N-by-N square and each
\* cell holds a live/dead boolean.  Live cells with 2 or 3 live neighbors survive;
\* dead cells with exactly 3 live neighbors are born; otherwise a cell dies/stays
\* dead.  The whole board updates simultaneously from one deterministic generation
\* to the next.

Pos == {p \in (1..N) \X (1..N)}
Neighbors(p) == {q \in Pos : q # p /\ (q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1) /\ (q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1)}
LiveCount(p) == Cardinality({q \in Neighbors(p) : cells[q]})

TypeOK ==
    /\ cells \in [Pos -> BOOLEAN]

Init ==
    /\ \E c \in [Pos -> BOOLEAN] : cells = c

Tick ==
    /\ cells' = [p \in Pos |-> IF cells[p]
                     THEN LiveCount(p) = 2 \/ LiveCount(p) = 3
                     ELSE LiveCount(p) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

====