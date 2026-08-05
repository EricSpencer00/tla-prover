---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Cell == {1, 2}
Positions == Cell \X Cell
Neighbors == {d \in Cell \X Cell : d[1] >= 0 /\ d[1] <= 1 /\ d[2] >= 0 /\ d[2] <= 1 /\ d # <<0, 0>>}

LiveNeighbors(p) == Cardinality({t \in Neighbors : alive[p[1] + t[1], p[2] + t[2]]})

TypeOK ==
    /\ alive \in [Positions -> BOOLEAN]

Init ==
    \E g \in [Positions -> BOOLEAN] : alive = g

Tick ==
    /\ alive' = [p \in Positions |-> LET n == LiveNeighbors(p) IN IF alive[p] THEN (n = 2 \/ n = 3) ELSE (n = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====