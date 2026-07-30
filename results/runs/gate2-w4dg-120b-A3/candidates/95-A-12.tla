---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cell

vars == <<cell>>

Positions == UNION {1..N} \X {1..N}

NeighborPos(p) == {q \in Positions : q # p /\ p[1] - q[1] \in -1..1 /\ p[2] - q[2] \in -1..1}

Init ==
    [p \in Positions |-> CHOOSE b \in BOOLEAN : TRUE]

Tick ==
    LET aliveCount(p) ==
        Cardinality({q \in NeighborPos(p) : cell[q]})
    IN
        [p \in Positions |-> IF cell[p] /\ aliveCount(p) \in {2, 3}
                               THEN TRUE
                               ELSE IF ~cell[p] /\ aliveCount(p) = 3
                                   THEN TRUE
                                   ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == \A p \in Positions : cell[p] \in BOOLEAN

====