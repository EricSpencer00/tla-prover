---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == 1 .. N
Positions == Cells \X Cells
None == N + 1

VARIABLES grid

vars == <<grid>>

\* Count the number of live (true) cells in a given set of positions.
CountTrue(S) == Cardinality({p \in S : grid[p]})

\* A cell has up to eight neighbors: directly adjacent horizontally,
\* vertically, and diagonally. Cells outside the grid are treated as dead.
Neighbors(p) ==
    {q \in Positions :
        /\ (q # p)
        /\ (q[1] >= 1 /\ q[1] <= N)
        /\ (q[2] >= 1 /\ q[2] <= N)
        /\ (q[1] - p[1]) \in {-1, 0, 1}
        /\ (q[2] - p[2]) \in {-1, 0, 1}}

InitCell(p) == CHOOSE v \in BOOLEAN : TRUE

Init ==
    /\ grid \in [Positions -> BOOLEAN]
    /\ \A p \in Positions : grid' = [grid EXCEPT ![p] = InitCell(p)]

\* Fully deterministic simultaneous update: a live cell with 2 or 3 live
\* neighbors survives; a dead cell with exactly 3 live neighbors is born;
\* all other cells die.
Tick ==
    /\ grid' = [p \in Positions |->
                    \/ (grid[p] /\ CountTrue(Neighbors(p)) \in {2, 3})
                    \/ (~grid[p] /\ CountTrue(Neighbors(p)) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK == grid \in [Positions -> BOOLEAN]

====