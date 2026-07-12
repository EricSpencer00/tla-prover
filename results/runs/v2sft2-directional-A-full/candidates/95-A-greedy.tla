---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
\* The set of all valid grid positions (row, column) where 1 <= row, col <= N
Positions == { [row \in 1..N, col \in 1..N] }

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLES Alive

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all eight possible relative neighbor offsets
NeighborOffsets == { [dr \in -1..1, dc \in -1..1] : \E dr \in -1..1, dc \in -1..1 : dr # 0 \/ dc # 0 }

\* Given a position p, return the set of neighbor positions that are inside the grid
Neighbors(p) == { [row \in 1..N, col \in 1..N] :
                  LET np == [row |-> p.row + dr, col |-> p.col + dc] IN
                  \E o \in NeighborOffsets : np = [row |-> p.row + o.dr, col |-> p.col + o.dc] }

\* Count the number of live neighbors of a position p
LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : Alive[q] })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == Alive \in [p \in Positions |-> BOOLEAN]

\* ----------------------------------------------------------------------
\* Next-state relation (simultaneous update)
\* ----------------------------------------------------------------------
Next ==
  \E NewAlive \in [p \in Positions |-> BOOLEAN] :
    \A p \in Positions :
      IF Alive[p] THEN
        NewAlive[p] = (LiveNeighborCount(p) = 2 \/ LiveNeighborCount(p) = 3)
      ELSE
        NewAlive[p] = (LiveNeighborCount(p) = 3)
    /\ Alive' = NewAlive

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Alive

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == Alive \in [p \in Positions |-> BOOLEAN]

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====