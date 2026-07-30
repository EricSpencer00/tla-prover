---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == [1 .. N, 1 .. N]

\* A cell has up to eight neighbors: the cells directly adjacent horizontally,
\* vertically, and diagonally. Cells outside the grid (outside the range
\* 1..N for either coordinate) are treated as dead (value zero) when counting
\* neighbors.
Neighbors(i, j) ==
  { <<x, y>> \in Cells :
      x >= i - 1 /\ x <= i + 1 /\ y >= j - 1 /\ y <= j + 1 /\ (x # i \/ y # j) }

TypeOK == \A i \in Cells : Cells[i] \in BOOLEAN

Init ==
  \E f \in [Cells -> BOOLEAN] : Cells = f

Next ==
  \E f \in [Cells -> BOOLEAN] :
    /\ \A i \in Cells :
         LET live == Cardinality({ c \in Neighbors(i[1], i[2]) : Cells[c] })
         IN IF Cells[i] THEN f[i] = (live = 2 \/ live = 3) ELSE f[i] = (live = 3)
    /\ Cells' = f

Tick == Next

Spec == Init /\ [][Tick]_Cells

====