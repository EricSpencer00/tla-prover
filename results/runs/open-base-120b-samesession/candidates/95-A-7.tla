---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets, TLC

CONSTANT N \* dimension of the square grid (N >= 1)

VARIABLES A

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Pos == [row : 1 .. N, col : 1 .. N]

\* Type invariant: A is a total function from positions to BOOLEAN
TypeOK == A \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Abs(x) == IF x >= 0 THEN x ELSE -x

Neighbors(p) == { q \in Pos :
                    q # p /\                     \* not the same cell
                    Abs(q.row - p.row) <= 1 /\ 
                    Abs(q.col - p.col) <= 1 }

LiveNeighborCount(p) ==
  Cardinality({ q \in Neighbors(p) : A[q] })

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init == 
  /\ A \in [Pos -> BOOLEAN]   \* any assignment of alive/dead cells

\* ----------------------------------------------------------------------
\* Next-state relation (simultaneous update)
\* ----------------------------------------------------------------------
Next ==
  /\ A' = [p \in Pos |-> 
            ( A[p] /\ (LiveNeighborCount(p) = 2 \/ LiveNeighborCount(p) = 3) )
            \/ (~A[p] /\ LiveNeighborCount(p) = 3) ]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<A>>

Spec == Init /\ [][Next]_vars

=============================================================================