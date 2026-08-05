---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Positions == 1..N
Dims == Positions \X Positions
Neighbors == {d \in {-1, 0, 1} \X {-1, 0, 1} : d # <<0, 0>>}

VARIABLES alive
vars == <<alive>>

TypeOK ==
    /\ alive \in [Dims -> BOOLEAN]

Init ==
    /\ alive = [p \in Dims |-> CHOOSE b \in BOOLEAN : TRUE]

NeighborsOf(p) ==
    {q \in Dims : <<q[1] - p[1], q[2] - p[2]>> \in Neighbors}

LiveNeighborCount(p) ==
    Cardinality({q \in NeighborsOf(p) : alive[q]})

NextAlive(p) ==
    LET n == LiveNeighborCount(p) IN
        IF alive[p] THEN n = 2 \/ n = 3
        ELSE n = 3

Tick ==
    /\ alive' = [p \in Dims |-> NextAlive(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====