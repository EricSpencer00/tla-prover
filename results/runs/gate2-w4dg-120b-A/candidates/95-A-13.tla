---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

CellsInGrid == {p \in (1..N) \X (1..N)}

RECURSIVE CountOnes(_)
CountOnes(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF x[2] THEN 1 ELSE 0) + CountOnes(S \ {x})

VARIABLES cells
vars == <<cells>>

LiveNeighbors(r, c) ==
  LET S == {x \in CellsInGrid :
               x[1] >= r - 1 /\ x[1] <= r + 1 /\ x[2] >= c - 1 /\ x[2] <= c + 1 /\ x # <<r, c>>}
  IN CountOnes({<<x[1], x[2], cells[x]>> : x \in S})

\* The transition relation is deterministic given the current grid: it is
\* computed from the current neighbor counts, not nondeterministically.
NextCell(r, c) ==
  LET n == LiveNeighbors(r, c) IN
    IF cells[r, c] /\ (n = 2 \/ n = 3) THEN TRUE
    ELSE IF ~ cells[r, c] /\ n = 3 THEN TRUE
    ELSE FALSE

TypeOK == cells \in [CellsInGrid -> BOOLEAN]

Init ==
  /\ cells \in [CellsInGrid -> BOOLEAN]

Tick ==
  /\ cells' = [p \in CellsInGrid |-> NextCell(p[1], p[2])]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====