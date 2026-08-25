---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N \* grid dimension (N-by-N)

VARIABLES grid

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Pos == 1..N \X 1..N
\* The state variable must always be a mapping from positions to booleans
TypeOK == grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Neighbors(p) ==
  { q \in Pos :
      (Abs(p[1] - q[1]) <= 1) /\ (Abs(p[2] - q[2]) <= 1) /\ q # p }

LiveNeighbors(p) ==
  Cardinality({ q \in Neighbors(p) : grid[q] })

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Next-state relation (simultaneous update)
\* ----------------------------------------------------------------------
Next ==
  /\ \A p \in Pos :
        LET ln == LiveNeighbors(p) IN
        grid'[p] = (grid[p] /\ (ln = 2 \/ ln = 3)) \/ (~grid[p] /\ ln = 3)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<grid>>

====