---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES cells

vars == <<cells>>

Positions == (1..N) \X (1..N)

Offgrid(p) == IF p \in Positions THEN cells[p] ELSE FALSE

Neighbors(p) == {q \in Positions : q # p /\ (q[1] - p[1])^2 + (q[2] - p[2])^2 <= 2}

TypeOK == cells \in [Positions -> BOOLEAN]

Init == cells = [p \in Positions |-> CHOOSE b \in BOOLEAN : TRUE]

Tick ==
    /\ \E f \in [Positions -> BOOLEAN] :
        /\ \A p \in Positions :
            LET alive == Cardinality({q \in Neighbors(p) : Offgrid(q)})
                cur == cells[p]
            IN f[p] = (IF cur /\ (alive = 2 \/ alive = 3) THEN TRUE ELSE IF ~cur /\ alive = 3 THEN TRUE ELSE FALSE)
        /\ cells' = f
    /\ UNCHANGED <<>>

Spec == Init /\ [][Tick]_vars

CellEvolutionIsDeterministic ==
    \A f1, f2 \in [Positions -> BOOLEAN] :
        (\A p \in Positions :
            LET alive == Cardinality({q \in Neighbors(p) : Offgrid(q)})
                cur == cells[p]
            IN f1[p] = (IF cur /\ (alive = 2 \/ alive = 3) THEN TRUE ELSE IF ~cur /\ alive = 3 THEN TRUE ELSE FALSE))
        =>
        \A p \in Positions : f1[p] = f2[p]

====