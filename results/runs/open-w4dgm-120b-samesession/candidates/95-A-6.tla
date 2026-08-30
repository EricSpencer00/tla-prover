---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

VARIABLES grid

vars == <<grid>>

Positions == (1..N) \X (1 .. N)

Within(p) == p[1] \in 1..N /\ p[2] \in 1..N

Offsets == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
            <<0, -1>>,            <<0, 1>>,
            <<1, -1>>,  <<1, 0>>, <<1, 1>>}

\* The eight positions surrounding a cell, filtered to those that actually lie
\* inside the N-by-N grid (outside the grid is treated as dead / zero value).
Neighbors(p) == {q \in Positions : Within(<<p[1] + q[1], p[2] + q[2]>>)}

CountLive(p) ==
    Cardinality({q \in Neighbors(p) : grid[q]})

TypeOK ==
    /\ grid \in [Positions -> BOOLEAN]

Init ==
    /\ grid \in [Positions -> BOOLEAN]

Tick ==
    /\ \E g \in [Positions -> BOOLEAN] :
         /\ \A p \in Positions :
              /\ g[p] = IF grid[p] /\ CountLive(p) \in {2, 3}
                         THEN TRUE
                         ELSE IF ~grid[p] /\ CountLive(p) = 3
                         THEN TRUE
                         ELSE FALSE
         /\ grid' = g

Next ==
    \/ Tick

Spec ==
    /\ Init
    /\ [][Next]_vars

====