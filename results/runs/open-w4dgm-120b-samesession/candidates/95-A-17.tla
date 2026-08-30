---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Positions == 1..N

Neighbors == {d \in [dr : -1..1, dc : -1..1] : d # [dr |-> 0, dc |-> 0]}

VARIABLES alive

vars == <<alive>>

TypeOK == alive \in [Positions \X Positions -> BOOLEAN]

Init ==
    /\ alive \in [Positions \X Positions -> BOOLEAN]

LiveNeighbors(p) ==
    Cardinality({d \in Neighbors : (p[1] + d.dr) \in Positions /\ (p[2] + d.dc) \in Positions /\ alive[p[1] + d.dr, p[2] + d.dc]})

Tick ==
    /\ alive' = [p \in Positions \X Positions |->
                    \/ (alive[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3))
                    \/ (~alive[p] /\ LiveNeighbors(p) = 3)]

Spec == Init /\ [][Tick]_vars

TypeOKInv == TypeOK

====