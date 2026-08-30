---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ZERO == 0 - 1

\* A cell is indexed by its row and column in the NxN grid.
Cell == 0..(N - 1)

\* grid[c] is TRUE iff the cell at position c is alive.
VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cell -> [Cell -> BOOLEAN]]

Init ==
    \E g \in [Cell -> [Cell -> BOOLEAN]] : grid = g

\* Neighbors of a cell: the 8 surrounding cells, staying within the grid.
Neighbors(c) ==
    {d \in Cell \X Cell : d # <<c[1], c[2]>> /\ (c[1] - 1 <= d[1] /\ d[1] <= c[1] + 1) /\ (c[2] - 1 <= d[2] /\ d[2] <= c[2] + 1)}

\* Count how many of cell c's neighbors are currently alive.
AliveNeighbors(c) ==
    LET f[S \in SUBSET (Cell \X Cell)] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN (IF grid[x[1]][x[2]] THEN 1 ELSE 0) + f[S \ {x}]
    IN f[Neighbors(c)]

\* The entire grid updates together, computed from the old grid.
Tick ==
    /\ \E g \in [Cell -> [Cell -> BOOLEAN]] :
        \A c \in Cell \X Cell :
            g[c[1]][c[2]] = IF grid[c[1]][c[2]]
                THEN \/ (AliveNeighbors(c) = 2) \/ (AliveNeighbors(c) = 3)
                ELSE (AliveNeighbors(c) = 3)
    /\ grid' = g
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

\* The automaton is fully deterministic: a given state has exactly one successor.
DeterministicStep ==
    \A s \in SUBSET vars :
        \A a1, a2 \in [vars -> BOOLEAN] :
            (a1 \in s /\ a2 \in s) => a1 = a2

====