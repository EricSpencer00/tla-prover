---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Positions == 1..N

Neighbors(p) ==
    { q \in (Positions \X Positions) :
        /\ q # p
        /\ ABS(q[1] - p[1]) <= 1
        /\ ABS(q[2] - p[2]) <= 1 }

LiveCount(p) ==
    Cardinality({ q \in Neighbors(p) : alive[q] })

Init ==
    /\ alive \in [Positions \X Positions -> BOOLEAN]

Tick ==
    /\ alive' = [p \in Positions \X Positions |-> (LiveCount(p) = 3 \/ (alive[p] /\ LiveCount(p) = 2))]
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ alive \in [Positions \X Positions -> BOOLEAN]

====