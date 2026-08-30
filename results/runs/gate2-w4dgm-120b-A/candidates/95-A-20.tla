---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N

Neighbours(p) ==
    {q \in Positions \X Positions :
        q # p /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1
                /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1}

AliveCount(p) == Cardinality({q \in Neighbours(p) : grid[q]})

Init ==
    /\ grid \in [Positions \X Positions -> BOOLEAN]

Tick ==
    /\ grid' = [p \in Positions \X Positions |->
                  IF grid[p]
                  THEN AliveCount(p) \in {2, 3}
                  ELSE AliveCount(p) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

====