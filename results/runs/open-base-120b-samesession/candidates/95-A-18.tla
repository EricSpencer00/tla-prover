---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLE A

(*--------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------*)

Cells == 1..N \X 1..N

Neighbors(p) == { q \in Cells :
                    (q[1] - p[1]) \in -1..1 /\ 
                    (q[2] - p[2]) \in -1..1 /\ 
                    q # p }

LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : A[q] })

Update(p) == (A[p] /\ (LiveNeighborCount(p) = 2 \/ LiveNeighborCount(p) = 3))
            \/ (~A[p] /\ LiveNeighborCount(p) = 3)

(*--------------------------------------------------------------------
  Init, Next, Spec
--------------------------------------------------------------------*)

Init == A \in [Cells -> BOOLEAN]

Next == A' = [p \in Cells |-> Update(p)]

Spec == Init /\ [][Next]_<<A>>

(*--------------------------------------------------------------------
  Invariant
--------------------------------------------------------------------*)

TypeOK == A \in [Cells -> BOOLEAN]

====