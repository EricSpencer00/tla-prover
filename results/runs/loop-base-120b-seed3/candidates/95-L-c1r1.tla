---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLES grid

(* ----------------------------------------------------------------------
   Utility definitions
   ---------------------------------------------------------------------- *)
Abs(i) == IF i >= 0 THEN i ELSE -i

(* ----------------------------------------------------------------------
   Definitions of positions and cells
   ---------------------------------------------------------------------- *)
Pos == 1..N
Cell == [row : Pos, col : Pos]      \* The set of all positions on the grid

(* ----------------------------------------------------------------------
   Neighborhood relation (8 neighbours, staying inside the grid)
   ---------------------------------------------------------------------- *)
Neighbors(p) ==
  { q \in Cell :
      /\ q # p
      /\ Abs(q.row - p.row) <= 1
      /\ Abs(q.col - p.col) <= 1 }

LiveNeighbors(g, p) ==
  Cardinality({ q \in Neighbors(p) : g[q] = TRUE })

(* ----------------------------------------------------------------------
   Cell update rule
   ---------------------------------------------------------------------- *)
UpdateCell(g, p) ==
  IF g[p] THEN
    (LiveNeighbors(g, p) = 2) \/ (LiveNeighbors(g, p) = 3)
  ELSE
    LiveNeighbors(g, p) = 3

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK == grid \in [Cell -> BOOLEAN]

(* ----------------------------------------------------------------------
   Initial state: any mapping from cells to Boolean
   ---------------------------------------------------------------------- *)
Init == grid \in [Cell -> BOOLEAN]

(* ----------------------------------------------------------------------
   Next-state relation: simultaneous update of all cells
   ---------------------------------------------------------------------- *)
Next ==
  \E gridPrime \in [Cell -> BOOLEAN] :
    /\ \A p \in Cell : gridPrime[p] = UpdateCell(grid, p)
    /\ grid' = gridPrime

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<grid>>

====