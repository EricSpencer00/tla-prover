---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == 1..N
Neighbors ==
    {
        <dx, dy> \in {-1, 0, 1} \X {-1, 0, 1} :
            dx # 0 \/ dy # 0
    }

VARIABLES cells

vars == <<cells>>

Valid(r, c) == r \in Positions /\ c \in Positions

Init ==
    \E f \in [Positions \X Positions -> BOOLEAN] : cells = f

Within(n) ==
    IF n \in Positions THEN n ELSE 0

NeighborCount(r, c) ==
    LET nlist == {<<Within(r + dx), Within(c + dy)>> : <<dx, dy>> \in Neighbors}
    IN Cardinality({p \in nlist : cells[p] = TRUE})

Next ==
    \E f \in [Positions \X Positions -> BOOLEAN] :
        \A p \in Positions \X Positions :
            LET cnt == NeighborCount(p[1], p[2])
            IN f[p] = (IF cells[p] = TRUE
                          THEN cnt = 2 \/ cnt = 3
                          ELSE cnt = 3)
              /\ cells' = f

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ cells \in [Positions \X Positions -> BOOLEAN]

====