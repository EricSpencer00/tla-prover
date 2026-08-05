---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANT N

VARIABLES cells

vars == << cells >>

GridPositions == 0..(N - 1)

TypeOK ==
    /\ cells \in [GridPositions \X GridPositions -> BOOLEAN]

Init ==
    /\ cells \in [GridPositions \X GridPositions -> BOOLEAN]

NeighborOffsets ==
    { << -1, -1 >>, << -1, 0 >>, << -1, 1 >>,
      << 0, -1 >>,              << 0, 1 >>,
      << 1, -1 >>, << 1, 0 >>, << 1, 1 >> }

LiveNeighbors(r, c) ==
    LET
        npos == { << r + dr, c + dc >> : << dr, dc >> \in NeighborOffsets }
        inside == { p \in npos : \A k \in {1, 2} : p[k] \in GridPositions }
        count == { p \in inside : cells[p] }
    IN
        Cardinality(count)

CreateAliveSet(r, c) ==
    LET
        npos == { << r + dr, c + dc >> : << dr, dc >> \in NeighborOffsets }
        inside == { p \in npos : \A k \in {1, 2} : p[k] \in GridPositions }
        aliveSet == { p \in inside : cells[p] }
    IN
        aliveSet

Tick ==
    /\ cells' = [r \in GridPositions, c \in GridPositions |-> LET k == LiveNeighbors(r, c) IN IF cells[<< r, c >>] /\ k \in {2, 3} THEN TRUE ELSE IF ~cells[<< r, c >>] /\ k = 3 THEN TRUE ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====