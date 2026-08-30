---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Grid positions: pairs of coordinates inside the N-by-N square.
Positions == (1..N) \X (1..N)

VARIABLES g

TypeOK == g \in [Positions -> BOOLEAN]

Init == \E assign \in [Positions -> BOOLEAN] : g = assign

Neighbors(p) == Cardinality({q \in Positions :
    /\ p # q
    /\ \E dr \in -1..1, dc \in -1..1 :
        dr # 0 \/ dc # 0
        /\ p[1] + dr = q[1]
        /\ p[2] + dc = q[2]})

LiveCount(p) == Cardinality({q \in Positions :
    /\ g[q]
    /\ \E dr \in -1..1, dc \in -1..1 :
        dr # 0 \/ dc # 0
        /\ p[1] + dr = q[1]
        /\ p[2] + dc = q[2]})

Tick == g' = [p \in Positions |-> IF g[p] /\ LiveCount(p) \in {2, 3}
                              THEN TRUE
                              ELSE IF ~g[p] /\ LiveCount(p) = 3
                              THEN TRUE
                              ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_g

vars == <<g>>

StateConstraint == TypeOK
====