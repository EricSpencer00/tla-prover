---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Alive == TRUE
Dead == FALSE

Positions == 1 .. N

\* The set of live neighbor positions for a grid position (r, c).
Neighbors(r, c) ==
  { <<i, j>> \in Positions \X Positions :
      ~(i = r /\ j = c) /\
      i >= r - 1 /\ i <= r + 1 /\ j >= c - 1 /\ j <= c + 1 }

LiveNeighbors(r, c) == Cardinality({ p \in Neighbors(r, c) : grid[p] })

TypeOK == grid \in [Positions \X Positions -> {Alive, Dead}]

Init ==
  /\ grid \in [Positions \X Positions -> {Alive, Dead}]

\* The Game of Life update is applied simultaneously to every cell on the grid.
Tick ==
  /\ grid' = [p \in Positions \X Positions |->
                LET n == LiveNeighbors(p[1], p[2]) IN
                  IF grid[p] = Alive
                    THEN IF n = 2 \/ n = 3 THEN Alive ELSE Dead
                    ELSE IF n = 3 THEN Alive ELSE Dead]
  /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====