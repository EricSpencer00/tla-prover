---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLE A

(*--- State space ---*)
Cell == (1 .. N) \X (1 .. N)

(*--- Helper definitions ---*)
Neighbors(p) == { q \in Cell :
                    (q # p) /\ 
                    (Abs(q[1] - p[1]) <= 1) /\ 
                    (Abs(q[2] - p[2]) <= 1) }

LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : A[q] })

(*--- Initialization ---*)
Init == A \in [Cell -> BOOLEAN]

(*--- Transition relation ---*)
Next ==
   \E A2 \in [Cell -> BOOLEAN] :
      /\ \A p \in Cell :
            A2[p] = IF A[p]
                     THEN (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
                     ELSE (LiveNeighbors(p) = 3)
      /\ A' = A2

(*--- Specification ---*)
Spec == Init /\ [][Next]_A

(*--- Invariant ---*)
TypeOK == A \in [Cell -> BOOLEAN]

====