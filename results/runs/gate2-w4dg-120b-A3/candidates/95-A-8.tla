---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Cells: each grid position holds a cell that is alive (TRUE) or dead (FALSE)
\* Grid: the NxN square grid of cells. Outside-cluster positions count as dead.
\* State: the grid mapping (i,j) to a Boolean (alive/dead), fully concrete.
\* Update: a fully deterministic synchronous step (Tick) computed from neighbor counts.

Positions == 1..N
Cells == [r \in Positions, c \in Positions]

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
  \E f \in [Cells -> BOOLEAN] : grid = f

\* Helper: count live neighbors of a cell, treating border positions as dead.
Neighbors(p) ==
  LET dr == {-1, 0, 1}  /\ dc == {-1, 0, 1}
      npos == { [r |-> p.r + dr[i], c |-> p.c + dc[i]] :
                i \in 1..3, j \in 1..3 |
                ~(dr[i] = 0 /\ dc[j] = 0) /\ p.r + dr[i] \in Positions /\ p.c + dc[j] \in Positions }
  IN Cardinality({ q \in npos : grid[q] })

LiveNext(p) ==
  LET c == Neighbors(p) IN
    IF grid[p] THEN (c = 2 \/ c = 3) ELSE (c = 3)

Next ==
  grid' = [p \in Cells |-> LiveNext(p)]

Spec == Init /\ [][Next]_vars

====