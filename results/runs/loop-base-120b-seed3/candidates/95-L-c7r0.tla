---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

VARIABLE Cells

Pos == 1..N \X 1..N

LiveNeighbors(c) ==
  Cardinality(
    {p \in Pos :
        p # c /\ 
        ABS(p[1] - c[1]) <= 1 /\ 
        ABS(p[2] - c[2]) <= 1 /\ 
        Cells[p]})

Init ==
  (* any assignment of booleans to all positions *)
  Cells \in [Pos -> BOOLEAN]

Next ==
  Cells' = [c \in Pos |
             IF Cells[c] THEN (LiveNeighbors(c) = 2 \/ LiveNeighbors(c) = 3)
             ELSE (LiveNeighbors(c) = 3)]

Spec == Init /\ [][Next]_<<Cells>>

TypeOK == Cells \in [Pos -> BOOLEAN]

====