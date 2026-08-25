---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLES grid

\* Domain of positions on the N×N grid
Domain == 1 .. N

\* Type invariant: grid maps each position to a Boolean (TRUE = alive, FALSE = dead)
TypeOK == grid \in [Domain -> BOOLEAN]

\* Initial state: any assignment of Booleans to the grid positions is allowed
Init == TypeOK

\* Predicate that holds when two positions are distinct neighbours
IsNeighbor(p, q) ==
    /\ p # q
    /\ Abs(p[1] - q[1]) <= 1
    /\ Abs(p[2] - q[2]) <= 1

\* Number of live neighbours of position p (cells outside the grid are ignored)
LiveNeighborCount(p) ==
    Cardinality({ q \in Domain : IsNeighbor(p, q) /\ grid[q] })

\* Simultaneous update of the whole grid (the "Tick" action)
Next ==
    /\ grid' = [p \in Domain |->
                IF (grid[p] /\ (LiveNeighborCount(p) = 2 \/ LiveNeighborCount(p) = 3))
                    \/ (~grid[p] /\ LiveNeighborCount(p) = 3)
                THEN TRUE
                ELSE FALSE]

\* The overall specification
Spec == Init /\ [][Next]_<<grid>>

====