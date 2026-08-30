---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == (1..N) \X (1..N)

VARIABLES aliveAt

vars == <<aliveAt>>

TypeOK ==
    /\ aliveAt \in [Positions -> BOOLEAN]

Init ==
    /\ \E f \in [Positions -> BOOLEAN] : aliveAt = f

AliveNeighbors(p) ==
    LET deltas == {[-1, 0], [1, 0], [0, -1], [0, 1],
                   [-1, -1], [-1, 1], [1, -1], [1, 1]} IN
    Cardinality({q \in Positions : aliveAt[q]
                 /\ \E d \in deltas : q = <p[1] + d[1], p[2] + d[2]>})

NextAlive(p) ==
    \/ aliveAt[p] /\ (AliveNeighbors(p) \in {2, 3})
    \/ ~aliveAt[p] /\ (AliveNeighbors(p) = 3)

Tick ==
    /\ aliveAt' = [p \in Positions |-> NextAlive(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====