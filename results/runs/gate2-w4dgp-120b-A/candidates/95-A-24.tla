---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

\* A cell is either alive or dead; the grid has fixed N-by-N boundaries.  Any
\* configuration of live/dead cells is a possible start, so Init nondeterministically
\* assigns each position's value.
Cells == {p \in 1..N : 1..N}
Positions == [r : 1..N, c : 1..N]
Neighbors == {[-1..1, -1..1] \ {{0, 0}}}

TypeOK ==
    /\ Cells = {p \in 1..N : 1..N}
    /\ UNCHANGED Cells

\* A neighbor is outside the grid boundary => its value counts as zero (dead).
\* The stability comment explains why this view is used: it is the only way TLC
\* can model the torus-free version described here.
Value(p) == IF p.r \in 1..N /\ p.c \in 1..N THEN Cells[p.r][p.c] ELSE FALSE

Init ==
    /\ Cells = [r \in 1..N, c \in 1..N |-> CHOOSE b \in BOOLEAN : TRUE]

\* The number of live neighbors is computed from the current (previous) grid state.
LiveNeighbors(p) ==
    Cardinality({d \in Neighbors : Value([r |-> p.r + d[1], c |-> p.c + d[2]])})

NextGen(p) ==
    LET n == LiveNeighbors(p) IN
        IF Cells[p.r][p.c]
        THEN IF n \in {2, 3} THEN TRUE ELSE FALSE
        ELSE IF n = 3 THEN TRUE ELSE FALSE

Tick ==
    /\ Cells' = [p \in 1..N : 1..N |-> NextGen(p)]

Next == Tick

Spec == Init /\ [][Next]_Cells

====