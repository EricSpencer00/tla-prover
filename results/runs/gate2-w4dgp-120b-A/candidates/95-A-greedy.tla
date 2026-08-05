---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Positions == 1..N
Neighbors == {[-1..1, -1..1]}

\* The cell at position (r, c) is alive iff grid[r, c] = TRUE.
TypeOK ==
  /\ grid \in [Positions \X Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions \X Positions -> BOOLEAN]

\* Count live neighbors of (r, c), treating cells outside the grid as dead.
LiveNeighbors(r, c) ==
  LET
    Count(S) ==
      IF S = {} THEN 0
      ELSE LET p == CHOOSE x \in S : TRUE IN
           (IF grid[p[1], p[2]] THEN 1 ELSE 0) + Count(S \ {p})
    Valid(p) == p[1] \in Positions /\ p[2] \in Positions
    Nbrs == { [r + dr, c + dc] : <<dr, dc>> \in Neighbors \ {[-0, -0]} }
  IN Count({p \in Nbrs : Valid(p)})

\* Every cell updates simultaneously based on its current neighbor count.
Tick ==
  /\ grid' = [p \in Positions \X Positions |->
        LET n == LiveNeighbors(p[1], p[2]) IN
          IF grid[p] /\ (n = 2 \/ n = 3) THEN TRUE
          ELSE IF ~grid[p] /\ n = 3 THEN TRUE
          ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====