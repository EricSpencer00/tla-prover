---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == cells

TypeOK == cells \in [0..(N - 1) \X 0..(N - 1) -> BOOLEAN]

\* Neighbor positions are the 8 surrounding cells (horizontal, vertical, diagonal);
\* positions outside the grid are considered dead (value zero).
NeighborsOf(p) ==
  {q \in 0..(N - 1) \X 0..(N - 1) : q # p /\ (\E dr \in {-1, 0, 1}, dc \in {-1, 0, 1} :
                                        dr # 0 \/ dc # 0 /\ q = <<p[1] + dr, p[2] + dc>>)}
LiveCount(p) == Cardinality({q \in NeighborsOf(p) : cells[q]})

\* Every cell updates simultaneously; a live cell with 2 or 3 live neighbors survives,
\* a dead cell with exactly 3 live neighbors becomes alive, otherwise the cell dies.
Tick == cells' = [p \in 0..(N - 1) \X 0..(N - 1) |->
                    IF cells[p] /\ (LiveCount(p) = 2 \/ LiveCount(p) = 3) THEN TRUE
                    ELSE IF ~cells[p] /\ LiveCount(p) = 3 THEN TRUE ELSE FALSE]

Init == cells \in [0..(N - 1) \X 0..(N - 1) -> BOOLEAN]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK
====