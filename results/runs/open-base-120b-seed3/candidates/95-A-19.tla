---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

\* ----------------------------------------------------------------------
\* Set of all cell positions on an N-by-N grid
\* ----------------------------------------------------------------------
Cells == 1..N \X 1..N

\* ----------------------------------------------------------------------
\* State variable: mapping each position to a Boolean (TRUE = alive)
\* ----------------------------------------------------------------------
VARIABLE A

\* ----------------------------------------------------------------------
\* Type invariant – A must always be a mapping from Cells to BOOLEAN
\* ----------------------------------------------------------------------
TypeOK == A \in [Cells -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Initial state: any Boolean assignment to every cell
\* ----------------------------------------------------------------------
Init == A \in [Cells -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Neighbor positions of a cell p = <<i, j>>
\* ----------------------------------------------------------------------
Neighbors(p) ==
    { q \in Cells :
        (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1) /\ q # p }

\* ----------------------------------------------------------------------
\* Number of live (TRUE) neighbors of p
\* ----------------------------------------------------------------------
LiveNeighbors(p) ==
    Cardinality( { q \in Neighbors(p) : A[q] } )

\* ----------------------------------------------------------------------
\* Update rule for a single cell according to Conway's Game of Life
\* ----------------------------------------------------------------------
CellUpdate(p) ==
    ( A[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3) )
    \/ ( ~A[p] /\ LiveNeighbors(p) = 3 )

\* ----------------------------------------------------------------------
\* Next-state relation: simultaneous update of all cells
\* ----------------------------------------------------------------------
Next ==
    A' = [p \in Cells |-> CellUpdate(p)]

\* ----------------------------------------------------------------------
\* Specification: initial condition and always‑next invariant
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<A>>

====