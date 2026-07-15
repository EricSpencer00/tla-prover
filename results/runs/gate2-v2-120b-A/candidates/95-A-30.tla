---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

(* ----------------------------------------------------------------------
   Set of all grid positions (row, column) where rows and columns start at 1
   ---------------------------------------------------------------------- *)
Pos == 1..N

Cells == Pos \X Pos

(* ----------------------------------------------------------------------
   Variable: mapping each cell to its state (TRUE = alive, FALSE = dead)
   ---------------------------------------------------------------------- *)
VARIABLE grid

(* ----------------------------------------------------------------------
   State predicate asserting that grid is a total function from Cells to BOOLEAN
   ---------------------------------------------------------------------- *)
TypeOK == grid \in [Cells -> BOOLEAN]

(* ----------------------------------------------------------------------
   Initial state: each cell nondeterministically assigned alive or dead
   ---------------------------------------------------------------------- *)
Init == grid \in [Cells -> BOOLEAN]

(* ----------------------------------------------------------------------
   Helper: compute the set of neighbor positions for a given cell,
   staying inside the grid (outside positions are ignored because they
   are considered dead)
   ---------------------------------------------------------------------- *)
Neighbors(p) == {
    <<i, j>> \in Cells :
        i \in Max(1, p[1]-1) .. Min(N, p[1]+1) /\
        j \in Max(1, p[2]-1) .. Min(N, p[2]+1) /\
        <<i, j>> # p
}

(* ----------------------------------------------------------------------
   Helper: number of alive neighbors of a cell p in the current grid
   ---------------------------------------------------------------------- *)
AliveNeighbors(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

(* ----------------------------------------------------------------------
   Deterministic update rule for a single cell
   ---------------------------------------------------------------------- *)
UpdateCell(p) ==
    IF grid[p] THEN
        /\ (AliveNeighbors(p) = 2) \/ (AliveNeighbors(p) = 3)
    ELSE
        /\ AliveNeighbors(p) = 3

(* ----------------------------------------------------------------------
   Simultaneous update of the entire grid
   ---------------------------------------------------------------------- *)
Next == /\ \A p \in Cells : grid[p] = UpdateCell(p)
        /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   Specification: Init followed by zero or more Next steps
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<grid>>

(* ----------------------------------------------------------------------
   The required invariant (type correctness) is already defined above.
   ---------------------------------------------------------------------- *)

=============================================================================