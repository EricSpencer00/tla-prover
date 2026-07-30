---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == (1..N) \X (1 .. N)

TypeOK ==
    /\ N \in Nat /\ N >= 1
    /\ grid \in [Positions -> BOOLEAN]

\* Count the live neighbors of (i, j). Positions outside the N-by-N grid
\* are treated as dead, so only grid positions are summed.
Neighbors(i, j) ==
    LET cells == {
        <<x, y>> \in Positions :
            x \in (i - 1) .. (i + 1) /\ y \in (j - 1) .. (j + 1)
            /\ ~(x = i /\ y = j)
    } IN
        Cardinality({c \in cells : grid[c] = TRUE})

Spec ==
    /\ TypeOK
    /\ \A p \in Positions : grid[p] \in {TRUE, FALSE}

\* The grid is filled nondeterministically at initialization: any assignment of
\* true/false to every position is an allowed start state.
Init ==
    /\ grid \in [Positions -> BOOLEAN]

\* Simultaneous update: each cell's next-state depends on the neighbor count
\* computed from the current grid, applied to the whole grid at once.
Tick ==
    /\ UNCHANGED N
    /\ grid' = [p \in Positions |-> IF
                    grid[p] = TRUE /\ (Neighbors(p[1], p[2]) = 2 \/ Neighbors(p[1], p[2]) = 3)
                \/ grid[p] = FALSE /\ Neighbors(p[1], p[2]) = 3
                THEN TRUE ELSE FALSE]

Next == Tick

====