---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cells == (1..N) \X (1..N)

\* The eight relative offsets of a cell's neighbors (including diagonals).
Neighbors == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>,
              << 0, -1>>,            << 0, 1>>,
              << 1, -1>>, << 1, 0>>, << 1, 1>>}

WithinGrid(p) == /\ p[1] \in 1..N
                 /\ p[2] \in 1..N

\* A live cell outside the grid is treated as dead (value zero).
Value(p) == IF WithinGrid(p) THEN grid[p] ELSE FALSE

Init ==
    \E assign \in [Cells -> BOOLEAN] :
        grid = assign

\* Fully deterministic: the next generation is uniquely determined by the current one.
Tick ==
    /\ grid' = [c \in Cells |->
                    LET liveCount == Cardinality({n \in Neighbors : Value(<<c[1] + n[1], c[2] + n[2]>>)})
                    IN IF grid[c]
                          THEN liveCount \in {2, 3}
                          ELSE liveCount = 3]
    /\ UNCHANGED <<N>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Cells -> BOOLEAN]

====