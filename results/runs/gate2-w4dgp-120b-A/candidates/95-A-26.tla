---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* A position on the square grid.
Positions == {1..N}

\* Each cell holds a boolean: TRUE = alive, FALSE = dead.  Cells outside the
\* grid (rows or columns outside 1..N) are treated as always dead.
VARIABLES cells

TypeOK == cells \in [Positions \X Positions -> BOOLEAN]

Init ==
  \E c \in [Positions \X Positions -> BOOLEAN] : cells = c

\* The set of up to eight neighboring positions of a given location (those that
\* fall within the grid's boundaries).
Neighbors(p) ==
  { q \in Positions \X Positions :
      q # p /\ q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1 /\ q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1 }

LiveCount(p) == Cardinality({ q \in Neighbors(p) : cells[q] })

\* Every cell is updated simultaneously from the current generation.
Tick ==
  /\ cells' = [p \in Positions \X Positions |->
                  IF cells[p] /\ (LiveCount(p) = 2 \/ LiveCount(p) = 3)
                  THEN TRUE
                  ELSE IF ~cells[p] /\ LiveCount(p) = 3
                  THEN TRUE
                  ELSE FALSE]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_cells

====