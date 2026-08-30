---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells
vars == <<cells>>

Cell == {1 .. N}
Pos == Cell \X Cell
None == [r |-> 0, c |-> 0]

Neighbors(p) ==
    {q \in Pos :
        /\ q # p
        /\ ABS(p[1] - q[1]) <= 1
        /\ ABS(p[2] - q[2]) <= 1}

CountAlive(p) ==
    Cardinality({q \in Neighbors(p) : cells[q]})

Init ==
    /\ cells \in [Pos -> BOOLEAN]

Tick ==
    /\ cells' = [p \in Pos |-> IF cells[p] /\ CountAlive(p) \in {2, 3}
                                   THEN TRUE
                                   ELSE IF ~cells[p] /\ CountAlive(p) = 3
                                   THEN TRUE
                                   ELSE FALSE]

Spec == Init /\ [][Tick]_vars

TypeOK ==
    /\ cells \in [Pos -> BOOLEAN]
====