---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == (1..N) \X (1..N)

Neighbors(p) == {
    q \in Cells :
        (q[1] # p[1] \/ q[2] # p[2])
        /\ (q[1] >= 1 /\ q[1] <= N /\ q[2] >= 1 /\ q[2] <= N)
        /\ (q[1] - p[1]) \in -1..1 /\ (q[2] - p[2]) \in -1..1
}

LiveNeighbors(p) == Cardinality({q \in Neighbors(p) : grid[q]})

TypeOK == grid \in [Cells -> BOOLEAN]

Init == \E f \in [Cells -> BOOLEAN] : grid = f

Tick ==
    /\ grid' = [p \in Cells |-> (grid[p] /\ (LiveNeighbors(p) \in {2, 3}))
                    \/ (~grid[p] /\ LiveNeighbors(p) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====