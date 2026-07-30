---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Live == "live"
Dead == "dead"

Positions == 1..N

VARIABLES cells

vars == <<cells>>

TypeOK == cells \in [Positions \X Positions -> {Live, Dead}]

\* A helper that treats outside-the-grid locations as always dead.  Outside
\* positions are the natural way to write neighbor clauses without a bunch of
\* bounds tests.
CellAt(i, j) == IF i \in Positions /\ j \in Positions THEN cells[i, j] ELSE Dead

LiveNeighbors(i, j) ==
  \/ IF CellAt(i - 1, j - 1) = Live THEN 1 ELSE 0
  \/ IF CellAt(i - 1, j) = Live THEN 1 ELSE 0
  \/ IF CellAt(i - 1, j + 1) = Live THEN 1 ELSE 0
  \/ IF CellAt(i, j - 1) = Live THEN 1 ELSE 0
  \/ IF CellAt(i, j + 1) = Live THEN 1 ELSE 0
  \/ IF CellAt(i + 1, j - 1) = Live THEN 1 ELSE 0
  \/ IF CellAt(i + 1, j) = Live THEN 1 ELSE 0
  \/ IF CellAt(i + 1, j + 1) = Live THEN 1 ELSE 0

\* The fate of a single cell at the next generation, given its live-neighbor
\* total and its current value.
NextCell(i, j) ==
  LET n == LiveNeighbors(i, j) IN
    IF cells[i, j] = Live
      THEN IF n = 2 \/ n = 3 THEN Live ELSE Dead
      ELSE IF n = 3 THEN Live ELSE Dead

Init == \E f \in [Positions \X Positions -> {Live, Dead}] : cells = f

\* Simultaneous update: the new grid is computed from the old one, not
\* incrementally.
Tick == cells' = [i \in Positions, j \in Positions |-> NextCell(i, j)]

Next == Tick

Spec == Init /\ [][Next]_vars

====