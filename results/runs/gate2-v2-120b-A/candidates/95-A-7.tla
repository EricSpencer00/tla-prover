---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* grid dimension, to be bound in the .cfg file

VARIABLE grid \* mapping from positions to Booleans (TRUE = alive, FALSE = dead)

(* Helper definitions *)
Pos == 1..N

AllPos == { <<i, j>> : i \in Pos, j \in Pos }

NeighborOffsets == { -1, 0, 1 }

Neighbors(p) ==
  LET i == p[1], j == p[2] IN
    { <<i + di, j + dj>> :
        di \in NeighborOffsets,
        dj \in NeighborOffsets,
        (di # 0) \/ (dj # 0),
        i + di \in Pos,
        j + dj \in Pos }

LiveNeighborCount(p) ==
  Cardinality( { q \in Neighbors(p) : grid[q] } )

(* Initialization *)
Init ==
  /\ grid \in [AllPos -> BOOLEAN]

(* Deterministic update rule *)
Tick ==
  /\ grid' = [p \in AllPos |-> 
        IF grid[p] THEN
            LET cnt == LiveNeighborCount(p) IN cnt = 2 \/ cnt = 3
        ELSE
            LiveNeighborCount(p) = 3
        ]

(* State transition relation *)
Next == Tick

(* Full specification *)
Spec == Init /\ [][Next]_<<grid>>

(* Type correctness invariant *)
TypeOK == grid \in [AllPos -> BOOLEAN]

====