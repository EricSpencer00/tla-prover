---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N
ASSUME N \in Nat

VARIABLES grid

Pos == { <<i, j>> : i \in 1..N, j \in 1..N }

Neighbors(p) == 
  LET i == p[1], j == p[2] IN
    { <<i + di, j + dj>> :
        di \in -1..1, dj \in -1..1,
        (di # 0 \/ dj # 0) /\ i + di \in 1..N /\ j + dj \in 1..N }

LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

Init == /\ grid \in [Pos -> BOOLEAN]

Next == 
  \E newgrid \in [Pos -> BOOLEAN] :
    /\ \A p \in Pos :
        LET cnt == LiveNeighborCount(p) IN
          newgrid[p] = ( (grid[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~grid[p] /\ cnt = 3) )
    /\ grid' = newgrid

Vars == <<grid>>

Spec == Init /\ [][Next]_Vars

TypeOK == grid \in [Pos -> BOOLEAN]

====