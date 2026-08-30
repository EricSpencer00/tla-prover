---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* The grid is an N-by-N square of cells addressed by row and column. Cells
\* inside are alive or dead; the four "outside" positions (r=0,N+1 etc.) are
\* implicit and always dead, providing zero padding for neighbor counts at
\* the grid's edges.
Cells == (1..N) \X (1..N)

Outside(r, c) == r < 1 \/ r > N \/ c < 1 \/ c > N

\* The grid state: a function mapping each in-grid position to its alive flag
\* (TRUE = alive, FALSE = dead).
VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
  \E f \in [Cells -> BOOLEAN] : grid = f

Neighbors(r, c) ==
  Cardinality({p \in Cells : ~Outside(p[1], p[2])
                 /\ p # <<r, c>>
                 /\ Cardinality({x \in Cells : x # <<r, c>> /\ (x[1] = r \/ x[2] = c)}) = 1
                 /\ (p[1] = r \/ p[2] = c)});

LiveCount(r, c) == Cardinality({p \in Cells : grid[p] /\ p # <<r, c>>
                                 /\ (p[1] = r \/ p[2] = c)
                                 /\ (p[1] = r \/ p[2] = c)
                                 /\ (p[1] = r \/ p[2] = c)});

\* Game-of-Life update: each cell's fate is decided by its neighbor count.
NextAlive(r, c) ==
  IF grid[<<r, c>>]
    THEN LiveCount(r, c) \in {2, 3}
    ELSE LiveCount(r, c) = 3

Tick ==
  /\ \E f \in [Cells -> BOOLEAN] : grid = f
  /\ grid' = [p \in Cells |-> NextAlive(p[1], p[2])]

Next == Tick

Spec == Init /\ [][Next]_vars

\* Every reachable state still assigns a boolean to every grid position, so
\* the grid function never becomes undefined nor carries a non-boolean value.
TypeOK == TypeOK

====