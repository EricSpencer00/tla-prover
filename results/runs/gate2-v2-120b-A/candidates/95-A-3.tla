---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N \* grid dimension (must be a positive natural number)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Cells == 1..N

Pos == [row : Cells, col : Cells]

\* Directions for the eight neighboring positions
Directions == {
  <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
  << 0, -1>>,           << 0, 1>>,
  << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* Neighbor positions of a given cell (may lie outside the grid)
NeighborPos(p) == { [row |-> p.row + d[1], col |-> p.col + d[2]]
                     : d \in Directions }

\* Live neighbor count, treating out‑of‑bounds positions as dead
LiveNeighbors(g, p) ==
  Cardinality({ nb \in NeighborPos(p) :
                 /\ 1 <= nb.row /\ nb.row <= N
                 /\ 1 <= nb.col /\ nb.col <= N
                 /\ g[nb] = TRUE })

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Type invariant (required as TypeOK)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state: each cell is nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN]
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Next-state action: simultaneous update according to Game of Life rules
\* ----------------------------------------------------------------------
Next ==
  \E newGrid \in [Pos -> BOOLEAN] :
    /\ newGrid \in [Pos -> BOOLEAN]
    /\ \A p \in Pos :
        LET n == LiveNeighbors(grid, p) IN
        IF grid[p] = TRUE THEN
          (* live cell survives with 2 or 3 neighbors *)
          newGrid[p] = (n = 2) \/ (n = 3)
        ELSE
          (* dead cell becomes alive with exactly 3 neighbors *)
          newGrid[p] = (n = 3)
    /\ grid' = newGrid

\* ----------------------------------------------------------------------
\* Specification (required as Spec)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_grid

\* ----------------------------------------------------------------------
\* Safety invariant (placeholder; no safety properties were specified)
\* ----------------------------------------------------------------------
SafetyInv == TRUE

\* ----------------------------------------------------------------------
\* The INVARIANT named in the .cfg file
\* ----------------------------------------------------------------------
INVARIANT == TypeOK

\* ----------------------------------------------------------------------
\* THEOREM to expose the main specification for TLC
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec

====