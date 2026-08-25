---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLE grid

(*--- State space ---*)
Pos == 1..N \X 1..N

(*--- Helper definitions ---*)
IsNeighbor(p, q) ==
  LET i  == p[1],  j  == p[2],
      i2 == q[1],  j2 == q[2] IN
    (i2 - i) \in {-1, 0, 1} /\ (j2 - j) \in {-1, 0, 1} /\ ~(i2 = i /\ j2 = j)

LiveNeighbors(p) ==
  Cardinality({ q \in Pos : IsNeighbor(p, q) /\ grid[q] })

(*--- Initialization ---*)
Init ==
  grid \in [Pos -> BOOLEAN]

(*--- Transition ---*)
Next ==
  /\ grid' = [p \in Pos |-> 
        IF grid[p] 
           THEN (LiveNeighbors(p) = 2) \/ (LiveNeighbors(p) = 3)
           ELSE LiveNeighbors(p) = 3
     ]

(*--- Specification ---*)
Spec == Init /\ [][Next]_<<grid>>

(*--- Invariant ---*)
TypeOK == grid \in [Pos -> BOOLEAN]

====