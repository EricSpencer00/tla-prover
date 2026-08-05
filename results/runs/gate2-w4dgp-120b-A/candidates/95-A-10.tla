---- MODULE GameOfLife ----
\* Conway's Game of Life on a fixed N-by-N grid. Each cell is alive or dead. At each
\* generation every cell updates simultaneously: a live cell with 2 or 3 live
\* neighbors survives, a dead cell with exactly 3 live neighbors becomes alive,
\* and all other cells die. Cells outside the grid count as dead.
EXTENDS Naturals

CONSTANTS N

\* The set of all positions inside the grid.
Positions == { p \in (1..N) \X (1..N) : TRUE }

VARIABLES alive

TypeOK == alive \in [Positions -> BOOLEAN]

\* Count the live neighbors of cell (i,j) among the eight surrounding positions,
\* all of which must itself be inside the grid to contribute.
neighbors(i, j) ==
  LET deltas == {<<dx, dy>> \in {{1, 0}, {-1, 0}, {0, 1}, {0, -1},
                                 {1, 1}, {1, -1}, {-1, 1}, {-1, -1}} :
                   TRUE } IN
  Cardinality({ dx \in {0, 1, -1}, dy \in {0, 1, -1} :
    <<dx, dy>> # <<0, 0>> /\ i + dx \in 1..N /\ j + dy \in 1..N /\ alive[i + dx, j + dy] })

CellSurvives(i, j) ==
  IF alive[i, j]
    THEN neighbors(i, j) \in {2, 3}
    ELSE neighbors(i, j) = 3

\* Simultaneous update: the next state of every cell depends only on the current
\* state of the entire grid, not on any intermediate values.
NextAlive(i, j) == CellSurvives(i, j)

Init == alive \in [Positions -> BOOLEAN]

\* A Tick advances every cell at once according to the Game of Life rules.
Tick == alive' = [i \in Positions |-> NextAlive(i[1], i[2])]

Spec == Init /\ [][Tick]_alive

====