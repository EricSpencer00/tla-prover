---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLES grid

(* The set of positions on the N×N board *)
Pos == 1..N \X 1..N

(* Type invariant: each position maps to a Boolean *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Initial state: any Boolean assignment to all positions *)
Init == grid \in [Pos -> BOOLEAN]

(* Neighboring positions of a given cell, respecting the fixed boundary *)
Neighbors(p) == { q \in Pos :
                    (q[1] - p[1]) \in -1..1 /\ 
                    (q[2] - p[2]) \in -1..1 /\ 
                    q # p }

(* Number of live (TRUE) neighbors of a cell *)
LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

(* Simultaneous update of the whole board *)
Next ==
    /\ grid' = [p \in Pos |->
                  IF grid[p]
                  THEN (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3)
                  ELSE (LiveNeighborCount(p) = 3)
               ]

(* Full specification: start in Init and repeatedly apply Next *)
Spec == Init /\ [][Next]_<<grid>>

====