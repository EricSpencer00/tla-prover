---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLE Grid

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

\* The set of all possible Grid states (used only for typing)
AllGrids == [pos \in Positions |-> BOOLEAN]

\* Neighborhood offsets (including diagonal neighbors)
NeighborOffsets == {
    << -1, -1>>, << -1, 0>>, << -1, 1>>,
    <<  0, -1>>,               <<  0, 1>>,
    <<  1, -1>>, <<  1, 0>>, <<  1, 1>>
}

\* Compute the neighbor positions of a given cell,
\* keeping only those that lie within the grid.
NeighborPositions(pos) ==
    { << r, c >> \in Positions :
        LET dr == pos[1] + << dr, dc >>[1] IN
        LET dc == pos[2] + << dr, dc >>[2] IN
        /\ dr \in Rows
        /\ dc \in Cols
        /\ << dr, dc >> \in Positions }

\* Number of live neighbors of a cell in the current Grid
LiveNeighborCount(pos) ==
    Cardinality({
        nb \in NeighborPositions(pos) :
            Grid[nb] = TRUE
    })

\* -------------------------------------------------
\* Initial predicate
\* -------------------------------------------------
Init ==
    /\ Grid \in AllGrids
    /\ \A pos \in Positions : Grid[pos] \in BOOLEAN

\* -------------------------------------------------
\* Next-state relation (the Tick action)
\* -------------------------------------------------
Tick ==
    \A pos \in Positions :
        LET cnt == LiveNeighborCount(pos) IN
        IF Grid[pos] = TRUE THEN
            /\ cnt \in {2, 3}
            /\ Grid' = [Grid EXCEPT ![pos] = TRUE]
        ELSE
            /\ cnt = 3
            /\ Grid' = [Grid EXCEPT ![pos] = TRUE]

\* -------------------------------------------------
\* Overall specification
\* -------------------------------------------------
Spec ==
    Init /\ [][Tick]_<<Grid>>

\* -------------------------------------------------
\* Type correctness invariant
\* -------------------------------------------------
TypeOK ==
    /\ Grid \in AllGrids
    /\ \A pos \in Positions : Grid[pos] \in BOOLEAN

====