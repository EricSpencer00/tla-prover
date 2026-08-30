---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

Nodes == 1..N

\* A position is a row-column pair inside the N-by-N grid.
Position == Nodes \X Nodes

\* A cell outside the grid is treated as dead when counting neighbors.
Outside == -1

\* A cell has up to eight neighbors: horizontally, vertically, diagonally adjacent.
Nbr(p) ==
    { q \in Position :
        q # p
        /\ (q[1] >= 1 /\ q[1] <= N)
        /\ (q[2] >= 1 /\ q[2] <= N)
        /\ (q[1] >= p[1] - 1 /\ q[1] <= p[1] + 1)
        /\ (q[2] >= p[2] - 1 /\ q[2] <= p[2] + 1)
    }

\* The live-neighbor count for a position, counting only in-grid live cells.
LiveCount(p) ==
    Cardinality({ q \in Nbr(p) : grid[q] })

TypeOK ==
    /\ grid \in [Position -> BOOLEAN]

Init ==
    \E g \in [Position -> BOOLEAN] : grid = g

\* Every cell updates simultaneously from the same neighbor counts.
Tick ==
    /\ \E g \in [Position -> BOOLEAN] :
        /\ \A p \in Position :
            /\ ~g[p] => (LiveCount(p) = 3) \/ (LiveCount(p) # 3)
            /\ g[p] => (LiveCount(p) = 2 \/ LiveCount(p) = 3)
        /\ grid' = g
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_grid

====