---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells

vars == <<cells>>

TypeOK == cells \in [1..N \X 1..N -> BOOLEAN]

Init == cells = [p \in 1..N \X 1..N |-> CHOOSE b \in BOOLEAN : TRUE]

AliveNeighbors(p) ==
  LET offsets == {{-1, -1}, {-1, 0}, {-1, 1},
                  {0, -1},           {0, 1},
                  {1, -1}, {1, 0}, {1, 1}} IN
  Cardinality({o \in offsets :
                 LET q == <<p[1] + o[1], p[2] + o[2]>> IN
                 /\ q[1] \in 1..N /\ q[2] \in 1..N
                 /\ cells[q] = TRUE})

Tick == cells' = [p \in 1..N \X 1..N |->
                    IF (cells[p] = TRUE /\ (AliveNeighbors(p) = 2 \/ AliveNeighbors(p) = 3))
                        \/ (cells[p] = FALSE /\ AliveNeighbors(p) = 3)
                    THEN TRUE ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====