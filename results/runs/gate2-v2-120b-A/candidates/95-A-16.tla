---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N \* grid dimension, to be supplied in the .cfg file

\* ----------------------------------------------------------------------
\* State variable: mapping each (row, col) in the N×N grid to a Boolean
\* indicating whether the cell is alive (TRUE) or dead (FALSE).
\* ----------------------------------------------------------------------
VARIABLE grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rows == 1..N
Cols == 1..N
Pos  == [r \in Rows, c \in Cols]

\* Set of the eight neighbor offsets (horizontal, vertical, diagonal)
NeighborOffsets == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    << 0, -1>>,           << 0, 1>>,
    << 1, -1>>, << 1, 0>>, << 1, 1>>
}

\* For a given position p, the set of its neighbor positions that lie
\* inside the grid; positions outside the grid are ignored (treated as dead).
Neighbors(p) == { [r |-> p.r + d[1], c |-> p.c + d[2]] :
                    d \in NeighborOffsets,
                    p.r + d[1] \in Rows,
                    p.c + d[2] \in Cols }

\* Number of live neighbors of position p in the current grid.
LiveNeighbors(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----------------------------------------------------------------------
\* Initial state: each cell is assigned nondeterministically TRUE (alive)
\* or FALSE (dead).  This yields any possible configuration.
\* ----------------------------------------------------------------------
Init ==
    /\ grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Deterministic update (Tick) applied simultaneously to all cells.
\* ----------------------------------------------------------------------
Tick ==
    /\ grid' =
        [p \in Pos |-> 
            IF grid[p] = TRUE THEN
                (* live cell survives with 2 or 3 live neighbors *)
                LiveNeighbors(p) \in {2, 3}
            ELSE
                (* dead cell becomes alive with exactly 3 live neighbors *)
                LiveNeighbors(p) = 3
        ]

\* ----------------------------------------------------------------------
\* Next-state relation: the only allowed transition is Tick.
\* ----------------------------------------------------------------------
Next == Tick

\* ----------------------------------------------------------------------
\* Behaviour specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (required by the .cfg file)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================