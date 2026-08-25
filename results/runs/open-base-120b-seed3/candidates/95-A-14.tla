---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLE A

Pos == 1 .. N
GridPos == Pos \X Pos

Abs(x) == IF x >= 0 THEN x ELSE -x

Adj(p, q) == (p # q) /\ (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1)

LiveNeighbours(p) == Cardinality({ q \in GridPos : Adj(p, q) /\ A[q] })

Next ==
  A' = [p \in GridPos |->
          IF (A[p] /\ (LiveNeighbours(p) = 2 \/ LiveNeighbours(p) = 3))
              \/ (~A[p] /\ LiveNeighbours(p) = 3)
          THEN TRUE ELSE FALSE]

Init == A \in [GridPos -> BOOLEAN]

Vars == <<A>>

Spec == Init /\ [][Next]_Vars

TypeOK == A \in [GridPos -> BOOLEAN]

====