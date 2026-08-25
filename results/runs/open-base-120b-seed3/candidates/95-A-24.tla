---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

(* Set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* Absolute value *)
Abs(x) == IF x < 0 THEN -x ELSE x

(* Type invariant: grid maps every position to a Boolean *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Initial state: any Boolean assignment to the grid *)
Init == TypeOK

(* Number of live neighbors of position p in the current grid *)
NeighborCount(p) ==
  LET alive == { q \in Pos :
                   q # p /\ 
                   Abs(q[1] - p[1]) <= 1 /\ 
                   Abs(q[2] - p[2]) <= 1 /\ 
                   grid[q] }
  IN Cardinality(alive)

(* Simultaneous update of the whole grid *)
Next ==
  grid' = [p \in Pos |-> 
            IF grid[p]
            THEN (NeighborCount(p) = 2) \/ (NeighborCount(p) = 3)
            ELSE (NeighborCount(p) = 3)]

Spec == Init /\ [][Next]_<<grid>>

====