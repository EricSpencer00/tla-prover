---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE grid

(* The set of all positions on the N×N grid *)
Pos == 1..N \X 1..N

(* The eight neighboring positions of a cell, restricted to the grid bounds *)
Neighbors(p) == { q \in Pos :
                    (q[1] = p[1] - 1 \/ q[1] = p[1] \/ q[1] = p[1] + 1) /\
                    (q[2] = p[2] - 1 \/ q[2] = p[2] \/ q[2] = p[2] + 1) /\
                    q # p }

(* Number of live (TRUE) neighbors of a cell *)
LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

(* The deterministic update rule for a single cell *)
CellUpdate(p) ==
    IF grid[p] THEN
        (LiveNeighborCount(p) = 2) \/ (LiveNeighborCount(p) = 3)
    ELSE
        (LiveNeighborCount(p) = 3)

(* Initialization: any assignment of TRUE/FALSE to each position is allowed *)
Init == grid \in [Pos -> BOOLEAN]

(* One step of the automaton: all cells are updated simultaneously *)
Next == /\ \A p \in Pos : grid'[p] = CellUpdate(p)

(* The full specification *)
Spec == Init /\ [][Next]_grid

(* Type invariant *)
TypeOK == grid \in [Pos -> BOOLEAN]

====