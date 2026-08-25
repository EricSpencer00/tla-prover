---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

VARIABLES grid

(* ---------------------------------------------------------------------- *)
(*   Sets and helper definitions                                            *)
(* ---------------------------------------------------------------------- *)

Pos == 1..N \X 1..N

NeighborOffsets == { <<di, dj>> :
                     di \in -1..1,
                     dj \in -1..1,
                     (di # 0) \/ (dj # 0) }

Neighbors(i, j) == { <<i + di, j + dj>> :
                     <<di, dj>> \in NeighborOffsets }

IsAlive(p) == IF p \in Pos THEN grid[p] ELSE FALSE

LiveCount(i, j) == Cardinality({ p \in Neighbors(i, j) : IsAlive(p) })

NextCell(p) ==
  LET i == p[1] IN
  LET j == p[2] IN
    IF grid[p] THEN
      (LiveCount(i, j) = 2) \/ (LiveCount(i, j) = 3)
    ELSE
      (LiveCount(i, j) = 3)

(* ---------------------------------------------------------------------- *)
(*   State predicates                                                       *)
(* ---------------------------------------------------------------------- *)

TypeOK == grid \in [Pos -> BOOLEAN]

Init == TypeOK

Next == /\ grid' = [p \in Pos |-> NextCell(p)]

Spec == Init /\ [] [Next]_<<grid>>

====