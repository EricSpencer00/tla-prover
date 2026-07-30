---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == 1 .. N

Positions == Cells \X Cells

VARIABLES alive

vars == <<alive>>

LiveNeighbors(p) ==
  LET nbs ==
        {<<p[1] + i, p[2] + j>> :
           i \in {-1, 0, 1}, j \in {-1, 0, 1},
           ~(i = 0 /\ j = 0),
           p[1] + i \in Cells, p[2] + j \in Cells}
  IN Cardinality({q \in nbs : alive[q]})

Init ==
  [p \in Positions |-> CHOOSE v \in BOOLEAN : TRUE]

\* Simultaneous update: the next value for every cell is computed from the
\* current grid before any cell actually flips, so the whole grid evolves
\* as one deterministic step (given the current state).
Next ==
  [p \in Positions |->
     (LET n == LiveNeighbors(p) IN (alive[p] /\ n \in {2, 3}) \/ (~alive[p] /\ n = 3))]

Spec == Init /\ [][Next]_vars

TypeOK == alive \in [Positions -> BOOLEAN]

====