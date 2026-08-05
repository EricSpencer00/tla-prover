---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Bounded grid: positions are pairs of row and column indices in 1..N. A
\* position outside the grid is treated as always dead when counting
\* neighbors, so parity works at the boundaries like the interior.
Positions == (1..N) \X (1..N)

VARIABLES grid

vars == <<grid>>

TypeOK ==
  /\ grid \in [Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions -> BOOLEAN]

Neighbors(p) == {q \in Positions : q # p /\ NatAbs(q[1] - p[1]) <= 1 /\ NatAbs(q[2] - p[2]) <= 1}

\* In-bounds neighbors of p that are alive; the eight-step rule is defined
\* on an infinite board, but here only in-bounds positions can be alive.
AliveCount(p) == Cardinality({q \in Neighbors(p) : grid[q]})

\* Simultaneous update of every cell: the new grid is a function of the
\* old grid, not a sequence of per-cell updates.
Tick ==
  /\ LET newgrid ==
         [p \in Positions |-> IF grid[p]
                              THEN AliveCount(p) \in {2, 3}
                              ELSE AliveCount(p) = 3]
     IN grid' = newgrid
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====