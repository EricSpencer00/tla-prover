---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

\* Set of all positions on the N×N grid
Pos == [i \in 1..N, j \in 1..N]

\* Type invariant: grid is a total mapping from positions to BOOLEAN
TypeOK == grid \in [Pos -> BOOLEAN]

\* Initial state: any mapping is allowed
Init == /\ TypeOK

\* Helper: number of live neighbours of a position p
NeighbourCount(p) ==
  LET nbrs == { q \in Pos :
                  /\ q # p
                  /\ ABS(q.i - p.i) <= 1
                  /\ ABS(q.j - p.j) <= 1 }
  IN Cardinality(nbrs)

\* One synchronous update step (Tick)
Next ==
  /\ \A p \in Pos:
        LET cnt == NeighbourCount(p) IN
        grid' [p] =
          (grid[p] /\ (cnt = 2 \/ cnt = 3)) \/ (~grid[p] /\ cnt = 3)

\* Full specification
Spec == Init /\ [][Next]_<<grid>>

====