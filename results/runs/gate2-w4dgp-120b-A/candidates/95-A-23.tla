---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

VARIABLES alive

vars == <<alive>>

CellPositions == 1..N

Positions == CellPositions \X CellPositions

Neighbors == {p \in Positions : p # <<1, 1>> /\ p # <<1, N>> /\ p # <<N, 1>> /\ p # <<N, N>>}

TypeOK ==
    /\ alive \in [Positions -> BOOLEAN]

Init ==
    /\ \E a \in [Positions -> BOOLEAN] : alive = a

OnGrid ==
    {p \in Positions : p[1] >= 1 /\ p[1] <= N /\ p[2] >= 1 /\ p[2] <= N}

NeighborCount(p) ==
    LET Candidates == {[p[1] + dr, p[2] + dc] : dr \in -1..1, dc \in -1..1, (dr, dc) # <<0, 0>>}
    IN Cardinality({q \in Candidates : q \in OnGrid /\ alive[q]})

Tick ==
    /\ alive' = [p \in Positions |->
                    LET c == NeighborCount(p) IN
                        IF alive[p] /\ (c = 2 \/ c = 3) THEN TRUE
                        ELSE IF ~alive[p] /\ c = 3 THEN TRUE
                        ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====