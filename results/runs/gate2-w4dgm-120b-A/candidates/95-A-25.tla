---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid
vars == <<grid>>

IsLive(p) == grid[p]

Neighbors == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    <<0, -1>>,           <<0, 1>>,
    <<1, -1>>, <<1, 0>>, <<1, 1>>
}

InBounds(p) == /\ p[1] \in 1..N
               /\ p[2] \in 1..N

LiveNeighbors(p) ==
    LET q == p[1]
        r == p[2]
    IN  Cardinality({d \in Neighbors : LET
                        pos == <<q + d[1], r + d[2]>>
                     IN  InBounds(pos) /\ IsLive(pos)})

Init ==
    /\ grid \in [1..N \X 1..N -> BOOLEAN]

Tick ==
    /\ grid' = [p \in 1..N \X 1..N |->
                  IF IsLive(p)
                     THEN LiveNeighbors(p) \in {2, 3}
                     ELSE LiveNeighbors(p) = 3]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ grid \in [1..N \X 1..N -> BOOLEAN]
====