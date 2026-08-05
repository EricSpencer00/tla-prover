---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Positions == {<row, col> \in [1..N \X 1..N]}

Neighbors ==
    {[1, 1], [1, 0], [1, -1], [0, 1], [0, -1], [-1, 1], [-1, 0], [-1, -1]}

NeighborsOf(pos) == {<pos[1] + d[1], pos[2] + d[2]> : d \in Neighbors}

AliveNeighbors(pos) ==
    Cardinality({n \in NeighborsOf(pos) : n \in Positions /\ alive[n]})

TypeOK == alive \in [Positions -> BOOLEAN]

Init ==
    /\ alive \in [Positions -> BOOLEAN]

Tick ==
    /\ alive' = [pos \in Positions |-> LET k == AliveNeighbors(pos) IN k = 3 \/ (alive[pos] /\ k = 2)]

Next == Tick

Spec == Init /\ [][Next]_vars

====