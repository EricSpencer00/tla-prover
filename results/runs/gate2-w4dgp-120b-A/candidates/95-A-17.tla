---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

RANGE == 0 .. (N - 1)

Positions == RANGE \X RANGE

\* Neighbors of a position: all grid positions that differ by at most one in both
\* coordinates, excluding the position itself.
Offsets == {d \in (-1 .. 1) \X (-1 .. 1) : d # <<0, 0>>}

InRange(p) == p[1] \in RANGE /\ p[2] \in RANGE

VARIABLES grid

vars == <<grid>>

TypeOK ==
    /\ grid \in [Positions -> BOOLEAN]

Init ==
    /\ grid \in [Positions -> BOOLEAN]

AliveNeighbors(p) ==
    Cardinality({ q \in Positions : <<p[1] + q[1], p[2] + q[2]>> \in Positions
                                   /\ q \in Offsets /\ grid[<<p[1] + q[1], p[2] + q[2]>>] })

Tick ==
    /\ grid' = [p \in Positions |-> LET n == AliveNeighbors(p) IN
                                      IF grid[p] /\ (n = 2 \/ n = 3) THEN TRUE
                                      ELSE IF ~grid[p] /\ n = 3 THEN TRUE
                                      ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====