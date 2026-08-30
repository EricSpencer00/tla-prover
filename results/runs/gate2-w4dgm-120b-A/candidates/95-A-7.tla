---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* The grid is an N-by-N square.  grid cells are indexed by row and column, and
\* each cell holds a boolean: TRUE means the cell is alive.
VARIABLES grid

vars == <<grid>>

GridCells == 1..N \X 1..N

\* A cell outside the grid (used when counting neighbors on the edge) is treated
\* as dead, i.e. contributes zero to the live-neighbor count.
Outside(r, c) == IF r \in 1..N /\ c \in 1..N THEN grid[r, c] ELSE FALSE

Nbrs(r, c) ==
    { <<rr, cc>> : rr \in {r - 1, r, r + 1}, cc \in {c - 1, c, c + 1}, <<rr, cc>> # <<r, c>> }

\* A cell's fate is decided by the standard Game of Life rules applied to the
\* full grid as it stands right now; the whole grid changes together.
LiveNbrs(r, c) == Cardinality({ p \in Nbrs(r, c) : Outside(p[1], p[2]) })
ConwayRule(r, c) ==
    IF grid[r, c]
        THEN IF LiveNbrs(r, c) \in {2, 3} THEN TRUE ELSE FALSE
        ELSE IF LiveNbrs(r, c) = 3 THEN TRUE ELSE FALSE

TypeOK == grid \in [GridCells -> BOOLEAN]

Init ==
    \E g \in [GridCells -> BOOLEAN] : grid = g

Tick == grid' = [p \in GridCells |-> ConwayRule(p[1], p[2])]

Next == Tick

Spec == Init /\ [][Next]_vars

\* No state space to bound here: every cell configuration is reachable from the
\* start, and each grid leads to exactly one next grid, so convergence is not
\* guaranteed and there is nothing to bound.
====