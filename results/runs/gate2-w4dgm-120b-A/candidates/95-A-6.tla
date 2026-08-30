---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* The grid is a mapping from each in-bounds position to a boolean (alive/dead).
\* The automaton is deterministic: once the initial configuration is chosen,
\* each successive generation is uniquely determined.
VARIABLES cells

vars == <<cells>>

Positions == 1..N

Succ(i) == IF i = N THEN 1 ELSE i + 1
Prev(i) == IF i = 1 THEN N ELSE i - 1

TypeOK == cells \in [Positions \X Positions -> BOOLEAN]

\* The eight neighboring positions of a cell, counting diagonals, with
\* wrap-around handling of the grid boundaries (periodic boundary condition).
Neighbors(p) == {
    <<Succ(p[1]), p[2]>>, <<Prev(p[1]), p[2]>>, <<p[1], Succ(p[2])>>, <<p[1], Prev(p[2])>>,
    <<Succ(p[1]), Succ(p[2])>>, <<Succ(p[1]), Prev(p[2])>>,
    <<Prev(p[1]), Succ(p[2])>>, <<Prev(p[1]), Prev(p[2])>>
}

CountAlive(p) ==
    Cardinality({q \in Neighbors(p) : cells[q]})

Init ==
    /\ cells \in [Positions \X Positions -> BOOLEAN]

\* Simultaneous update: every cell's new state depends on the count computed
\* from the CURRENT generation, so the partner's generation always moves forward.
Tick ==
    /\ \E newCells \in [Positions \X Positions -> BOOLEAN] :
        /\ \A p \in Positions \X Positions :
            newCells[p] = IF cells[p] THEN (CountAlive(p) \in {2, 3})
                         ELSE (CountAlive(p) = 3)
        /\ cells' = newCells

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)

\* No hidden danger: cells is always a total mapping from each position to a
\* boolean value; no cell is ever lost or duplicated in the mapping.
TypeOK == cells \in [Positions \X Positions -> BOOLEAN]

====