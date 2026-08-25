---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE cells

Pos == 1..N X 1..N

AreNeighbors(p, q) == (p[1] - q[1]) \in -1..1 /\ (p[2] - q[2]) \in -1..1 /\ p # q

LiveNeighborCount(p) == Cardinality({ q \in Pos : AreNeighbors(p, q) /\ cells[q] })

Init == cells \in [Pos -> BOOLEAN]

Next == cells' = [p \in Pos |-> 
                IF cells[p] 
                THEN (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3) 
                ELSE (LiveNeighborCount(p) = 3)
               ]

Spec == Init /\ [][Next]_<<cells>>

TypeOK == cells \in [Pos -> BOOLEAN]

====