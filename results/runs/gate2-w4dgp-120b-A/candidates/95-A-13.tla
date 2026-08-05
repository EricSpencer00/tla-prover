---- MODULE GameOfLife ----
EXTENDS Naturals
CONSTANTS N

\* A Conway's Game of Life grid. Grid is N-by-N; positions outside the grid
\* are dead, which is what the neighbor-counting function below enforces.
\* Each cell is a boolean (TRUE = alive, FALSE = dead). Tick updates the
\* whole grid simultaneously; there are no choices once the initial
\* configuration is fixed.

VARIABLES grid

TypeOK == grid \in [1..N \X 1..N -> BOOLEAN]

Init ==
  /\ grid \in [1..N \X 1..N -> BOOLEAN]

\* A cell's alive neighbors; positions outside the N-by-N grid are dead.
Neighbors(x) ==
  LET f(p) == IF p \in (1..N \X 1..N) /\ grid[p] THEN 1 ELSE 0
  IN LET deltas == {-1, 0, 1}
     IN LET positions == { <<x[1] + di, x[2] + dj>> : di \in deltas, dj \in deltas, ~(di = 0 /\ dj = 0) }
        IN LET np == {p \in positions : p \in (1..N \X 1..N)}
           IN LET vals == { f(p) : p \in np }
              IN IF vals = {} THEN 0 ELSE CHOOSE k \in vals : \A e \in vals : k <= e

\* The Game of Life update rule: a dead cell with exactly three live
\* neighbors is born; a live cell with two or three live neighbors
\* survives; otherwise it dies.
Next ==
  /\ \E newgrid \in [1..N \X 1..N -> BOOLEAN] :
       /\ \A x \in (1..N \X 1..N) :
            LET n == Neighbors(x) IN newgrid[x] = IF n = 3 OR (grid[x] /\ n = 2) THEN TRUE ELSE FALSE
       /\ grid' = newgrid

NextStep == Next

Spec == Init /\ [][NextStep]_grid

====