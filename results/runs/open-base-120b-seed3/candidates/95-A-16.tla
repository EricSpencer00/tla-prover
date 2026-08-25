---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N \* dimension of the square grid (N \in Nat)

VARIABLES grid

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Cells == 1..N \X 1..N

TypeOK == grid \in [Cells -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsNeighbor(p, q) ==
    /\ (p[1] - q[1]) \in -1..1
    /\ (p[2] - q[2]) \in -1..1
    /\ p # q

LiveNeighbors(p) ==
    Cardinality({ q \in Cells : IsNeighbor(p, q) /\ grid[q] })

WillBeAlive(p) ==
    IF grid[p] THEN
        LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3
    ELSE
        LiveNeighbors(p) = 3

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ TypeOK
    /\ grid \in [Cells -> BOOLEAN]   \* each cell nondeterministically alive or dead

\* ----------------------------------------------------------------------
\* Next-state relation (simultaneous update)
\* ----------------------------------------------------------------------
Next ==
    /\ grid' = [p \in Cells |-> WillBeAlive(p)]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<grid>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK

====