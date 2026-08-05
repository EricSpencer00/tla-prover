---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive
vars == <<alive>>

Positions == {p \in 1..N \X 1..N}

Neighbors(p) ==
    {q \in Positions : q # p /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1 /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1}

LiveNeighborsOf(p) == Cardinality({q \in Neighbors(p) : alive[q]})

TypeOK == alive \in [Positions -> BOOLEAN]

Init ==
    /\ alive \in [Positions -> BOOLEAN]

Tick ==
    /\ alive' = [p \in Positions |-> IF alive[p] /\ (LiveNeighborsOf(p) = 2 \/ LiveNeighborsOf(p) = 3)
                                   THEN TRUE
                                   ELSE IF ~alive[p] /\ LiveNeighborsOf(p) = 3
                                        THEN TRUE
                                        ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====