---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == (1..N) \X (1 .. N)

Alive == 1
Dead == 0

VARIABLES cells

vars == <<cells>>

TypeOK == cells \in [Positions -> {Alive, Dead}]

Init == cells = [p \in Positions |-> IF RandomElement({True, False}) THEN Alive ELSE Dead]

NeighborDirs == {
    <<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
    <<0, -1>>,            <<0, 1>>,
    <<1, -1>>,  <<1, 0>>, <<1, 1>>
}

LiveNeighbors(p) ==
    LET Count(S) ==
        IF S = {} THEN 0
        ELSE LET q == CHOOSE y \in S : TRUE IN cells[q] + Count(S \ {q})
    IN Count({q \in Positions :
                EXISTS d \in NeighborDirs :
                    LET c == <<p[1] + d[1], p[2] + d[2]>> IN c = q})

LiveNext(p) ==
    LET n == LiveNeighbors(p) IN
        IF cells[p] = Alive THEN IF n = 2 \/ n = 3 THEN Alive ELSE Dead
        ELSE IF n = 3 THEN Alive ELSE Dead

Tick == cells' = [p \in Positions |-> LiveNext(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====