---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == 1..N

VARIABLES cells
vars == << cells >>

TypeOK ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

NeighborCount(p) ==
  LET
    deltas == {-1, 0, 1}
    nbrs == { << p[1] + dr, p[2] + dc >> : dr \in deltas, dc \in deltas
                : (dr # 0 \/ dc # 0)
                /\ p[1] + dr \in Positions /\ p[2] + dc \in Positions }
  IN
    Cardinality({ q \in nbrs : cells[q] })

Init ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Tick ==
  /\ cells' = [p \in Positions \X Positions |-> IF cells[p]
        THEN (NeighborCount(p) = 2 \/ NeighborCount(p) = 3)
        ELSE (NeighborCount(p) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====