---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(*--- Helper definitions ---*)
Offsets == { <<di, dj>> : di \in -1..1, dj \in -1..1, ~ (di = 0 /\ dj = 0) }

(*--- Type invariant ---*)
TypeOK == grid \in [ (1..N) \X (1..N) -> BOOLEAN ]

(*--- Initial state ---*)
Init == TypeOK

(*--- Neighbor counting ---*)
LiveNeighbors(g, i, j) ==
  LET nbrs == { <<i+di, j+dj>> :
                 <<di, dj>> \in Offsets /\
                 1 <= i+di /\ i+di <= N /\
                 1 <= j+dj /\ j+dj <= N }
  IN Cardinality( { p \in nbrs : g[p] } )

(*--- Next-state relation ---*)
Next ==
  /\ grid' = [i \in 1..N, j \in 1..N |-> 
        LET cnt == LiveNeighbors(grid, i, j) IN
          IF grid[i, j] THEN (cnt = 2) \/ (cnt = 3) ELSE cnt = 3
      ]
  /\ UNCHANGED <<>>

(*--- Specification ---*)
Spec == Init /\ [][Next]_<<grid>>

====