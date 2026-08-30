---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Positions == 1..N
Variables == [pos: {<<r, c>> : r \in Positions, c \in Positions}}, val: BOOLEAN]

\* The grid is a set of {pos, val} records so that each update can freely
\* recompute the whole generation without disturbing the old one.
\* This is what makes the simultaneous update well-defined.
VARIABLES grid

vars == <<grid>>

TypeOK ==
    /\ grid \subseteq {<<r, c>> : r \in Positions, c \in Positions}}
    /\ \A p \in grid : p.val \in BOOLEAN

Init ==
    \E G \in SUBSET {<<r, c>> : r \in Positions, c \in Positions}} :
        /\ grid = G
        /\ \A p \in G : p.val \in BOOLEAN

\* Helper: the eight neighboring coordinates of a grid position.
Neighbors(p) == {
    <<p[1] - 1, p[2] - 1>>, <<p[1] - 1, p[2]>>, <<p[1] - 1, p[2] + 1>>,
    <<p[1],     p[2] - 1>>,                 <<p[1],     p[2] + 1>>,
    <<p[1] + 1, p[2] - 1>>, <<p[1] + 1, p[2>>, <<p[1] + 1, p[2] + 1>>
}

\* Any position outside the grid is treated as dead; it simply does not
\* appear in "grid", and the filter below skips it.
LiveAt(p) == \E q \in grid : q.pos = p /\ q.val

LiveNeighbors(p) ==
    Cardinality({q \in Neighbors(p) : LiveAt(q)})

\* Every cell is updated in the same step, based on the old generation only.
Tick ==
    /\ \E G \in SUBSET {<<r, c>> : r \in Positions, c \in Positions}} :
        /\ grid' = {<<p[1], p[2]>> : p \in {q \in {<<r, c>> : r \in Positions, c \in Positions}}
                                   : LET cnt == LiveNeighbors(p)
                                     IN IF cnt = 3 \/ (LiveAt(p) /\ cnt = 2) THEN TRUE ELSE FALSE}}
    /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====