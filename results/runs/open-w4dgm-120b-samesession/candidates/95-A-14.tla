---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N
Cells == Positions \X Positions

InitF(p) == IF p \in Cells THEN BOOLEAN ELSE FALSE

TypeOK ==
    /\ grid \in [Cells -> BOOLEAN]

Init ==
    /\ \E g \in [Cells -> BOOLEAN] : grid = g

NeighborsAlive(x, y) ==
    LET nb == {<<x + dx, y + dy>> : dx \in -1..1, dy \in -1..1, (dx, dy) # <<0, 0>>}
        alive(n) == IF n \in Cells /\ grid[n] THEN 1 ELSE 0
    IN alive(<<x, y>>) + alive(x - 1, y) + alive(x + 1, y)
       + alive(x, y - 1) + alive(x, y + 1)
       + alive(x - 1, y - 1) + alive(x - 1, y + 1)
       + alive(x + 1, y - 1) + alive(x + 1, y + 1)

LiveRule(c) ==
    LET cnt == NeighborsAlive(c[1], c[2])
    IN IF grid[c]
       THEN cnt = 2 \/ cnt = 3
       ELSE cnt = 3

Tick ==
    /\ \E g \in [Cells -> BOOLEAN] :
        /\ \A c \in Cells : g[c] = LiveRule(c)
        /\ grid' = g
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====