---- MODULE GameOfLife ----
EXTENDS Naturals, TLC

CONSTANT N

VARIABLE grid

Pos == 1..N \X 1..N

Abs(x) == IF x >= 0 THEN x ELSE -x

NeighborSet(p) == { q \in Pos :
                     p # q /\ 
                     Abs(p[1] - q[1]) <= 1 /\ 
                     Abs(p[2] - q[2]) <= 1 }

LiveCount(p) == Cardinality({ q \in NeighborSet(p) : grid[q] })

Init == grid \in [Pos -> BOOLEAN]

Next == /\ \A p \in Pos :
            grid'[p] = IF grid[p] 
                         THEN (LiveCount(p) = 2 \/ LiveCount(p) = 3)
                         ELSE (LiveCount(p) = 3)

Spec == Init /\ [][Next]_<<grid>>

TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================