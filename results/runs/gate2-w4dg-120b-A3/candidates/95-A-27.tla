---- MODULE GameOfLife ----
\* Conway's Game of Life on a square grid.  Each Tick updates all cells
\* simultaneously from their current neighbor counts.  Cells outside the
\* grid are treated as dead for neighbor-counting.  Any grid
\* configuration is a possible initial state.
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Cells == (1..N) \X (1..N)

Outside == (N + 1)
Off(x) == IF x \in Cells THEN cells[x] ELSE FALSE

Neighbors(x) ==
  LET f[y \in {-1, 0, 1}, z \in {-1, 0, 1}] ==
    LET p == <<x[1] + y, x[2] + z>> IN
      IF y = 0 /\ z = 0 THEN 0
      ELSE IF p[1] \in 1..N /\ p[2] \in 1..N THEN IF cells[p] THEN 1 ELSE 0
      ELSE 0
  IN f[-1, -1] + f[-1, 0] + f[-1, 1]
     + f[0, -1] + f[0, 1]
     + f[1, -1] + f[1, 0] + f[1, 1]

\* The next-state relation is deterministic: NextGrid is uniquely defined
\* from the current grid, and Tick advances to it.
NextGrid ==
  [x \in Cells |-> IF cells[x]
                    THEN (Neighbors(x) = 2) \/ (Neighbors(x) = 3)
                    ELSE Neighbors(x) = 3]

TypeOK == cells \in [Cells -> BOOLEAN]

Init ==
  /\ cells \in [Cells -> BOOLEAN]

Tick == cells' = NextGrid

Next == Tick

Spec == Init /\ [][Next]_vars
====