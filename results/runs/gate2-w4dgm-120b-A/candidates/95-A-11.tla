---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == 1..N

VARIABLES cells

vars == <<cells>>

Succ(x) == IF x < N THEN x + 1 ELSE x
Prev(x) == IF x > 1 THEN x - 1 ELSE x

TypeOK ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ cells \in [Positions \X Positions -> BOOLEAN]

LiveNeighbors(i, j) ==
  LET neighs == {
        <<r, c>> \in Positions \X Positions :
          r # i \/ c # j
      }
  IN Cardinality({p \in neighs : cells[p]})

Tick ==
  /\ cells' = [p \in Positions \X Positions |->
                 LET cnt == LiveNeighbors(p[1], p[2])
                 IN IF cells[p] /\ (cnt = 2 \/ cnt = 3) THEN TRUE
                    ELSE IF ~cells[p] /\ cnt = 3 THEN TRUE
                    ELSE FALSE]

Next == Tick \/ UNCHANGED cells

Spec == Init /\ [][Next]_vars

TypeOKOK == TypeOK
====