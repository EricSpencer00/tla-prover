---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

(* ----------------------------------------------------------------------
   Definition of the set of cell positions
   ---------------------------------------------------------------------- *)
Cell == [row : 1..N, col : 1..N]

(* ----------------------------------------------------------------------
   Helper: the eight neighboring positions of a cell (within the grid)
   ---------------------------------------------------------------------- *)
Neighbors(p) == { q \in Cell :
                    (q.row # p.row \/ q.col # p.col) /\               \* not the cell itself
                    Abs(q.row - p.row) <= 1 /\ Abs(q.col - p.col) <= 1 }

(* ----------------------------------------------------------------------
   Number of live neighbours of a cell in the current grid
   ---------------------------------------------------------------------- *)
LiveNeighbors(g, p) == Cardinality( { q \in Neighbors(p) : g[q] } )

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK == grid \in [Cell -> BOOLEAN]

(* ----------------------------------------------------------------------
   Initial state: any assignment of booleans to the cells
   ---------------------------------------------------------------------- *)
Init == grid \in [Cell -> BOOLEAN]

(* ----------------------------------------------------------------------
   Transition: simultaneous update of all cells according to Game of Life rules
   ---------------------------------------------------------------------- *)
Next ==
    \E grid' \in [Cell -> BOOLEAN] :
        /\ \A p \in Cell :
               grid'[p] =
                 IF grid[p] THEN
                     (LiveNeighbors(grid, p) = 2) \/ (LiveNeighbors(grid, p) = 3)
                 ELSE
                     LiveNeighbors(grid, p) = 3
        /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<grid>>

====