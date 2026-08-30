---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Positions == 1..N

\* The grid is a fixed N-by-N square of cells; each cell holds a boolean
\* saying whether it is alive (TRUE) or dead (FALSE).
VARIABLES cells

vars == << cells >>

TypeOK ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Neighbors(r, c) ==
  { << i, j >> \in Positions \X Positions :
      i # r \/ j # c /\ i \in {r - 1, r, r + 1} /\ j \in {c - 1, c, c + 1} }

\* Because the grid has hard boundaries, only positions inside the grid are
\* ever considered neighbors; everything outside is simply absent.
LiveCount(r, c) ==
  Cardinality({ p \in Neighbors(r, c) : cells[p] })

Tick ==
  /\ cells' = [p \in Positions \X Positions |->
                 IF cells[p]
                 THEN LiveCount(p[1], p[2]) \in {2, 3}
                 ELSE LiveCount(p[1], p[2]) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

====