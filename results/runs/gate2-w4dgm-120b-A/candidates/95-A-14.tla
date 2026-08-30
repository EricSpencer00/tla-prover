---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES alive

TypeOK == alive \in [1..N \X 1..N -> BOOLEAN]

\* A cell outside the grid boundary is treated as dead (value zero) for neighbor counting.
Neighbors(r, c) == {<<rr, cc>> \in (1..N) \X (1..N) :
                       rr \in {r-1, r, r+1} /\ cc \in {c-1, c, c+1} /\ ~(rr = r /\ cc = c)}

LiveCount(r, c) == Cardinality({p \in Neighbors(r, c) : alive[p]})

Init == alive = [p \in 1..N \X 1..N |-> CHOOSE b \in BOOLEAN : TRUE]

\* Simultaneous update: every cell is recomputed from the same generation's neighbor counts.
Tick == alive' = [p \in 1..N \X 1..N |-> IF alive[p] /\ LiveCount(p[1], p[2]) \in {2, 3}
                                             THEN TRUE
                                             ELSE IF ~alive[p] /\ LiveCount(p[1], p[2]) = 3
                                             THEN TRUE
                                             ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_alive

TypeOKInv == TypeOK

====