---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
Pos == (1..N) \X (1..N)

(* Absolute value *)
Abs(x) == IF x >= 0 THEN x ELSE -x

(* Two distinct positions are neighbors if they differ by at most 1 in each coordinate *)
Neighbor(p, q) == (p # q) /\ (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1)

(* Number of live neighbours of position p *)
Count(p) == Cardinality({ q \in Pos : Neighbor(p, q) /\ grid[q] })

(* The update rule for a single cell *)
Update(p) == (grid[p] /\ (Count(p) = 2 \/ Count(p) = 3)) \/ (~grid[p] /\ Count(p) = 3)

(* Initial state: any assignment of booleans to the grid *)
Init == grid \in [Pos -> BOOLEAN]

(* Simultaneous update of the whole grid *)
Next ==
  \E newgrid \in [Pos -> BOOLEAN] :
    /\ \A p \in Pos : newgrid[p] = Update(p)
    /\ grid' = newgrid

(* Overall specification *)
Spec == Init /\ [] [Next]_grid

(* Type invariant *)
TypeOK == grid \in [Pos -> BOOLEAN]

====