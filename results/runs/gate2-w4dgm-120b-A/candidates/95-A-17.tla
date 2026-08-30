---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES grid

Cells == [row : 1..N, col : 1..N]
Neighbors == {1, 2, 3, 4, 5, 6, 7, 8}

\* A cell at a position strictly outside the N-by-N grid is treated as dead.
InBounds(c) == c.row \in 1..N /\ c.col \in 1..N

\* Wraps a coordinate one step outward; used to refer to a neighbor position
\* that may fall outside the grid, which the spec treats as having value 0.
OffGrid(c) == [row |-> c.row + 1, col |-> c.col + 1]

\* Sum of the boolean values of a cell's eight neighboring positions.
\* Because cells outside the grid are dead (value 0), OffGrid(c) is safe
\* to refer to regardless of whether it is inside or outside the grid.
Ones(c) ==
  grid[OffGrid(c)] + grid[[row |-> c.row + 1, col |-> c.col]]
    + grid[[row |-> c.row + 1, col |-> c.col - 1]]
    + grid[[row |-> c.row + 1, col |-> c.col + 1]]
    + grid[[row |-> c.row, col |-> c.col - 1]]
    + grid[[row |-> c.row, col |-> c.col + 1]]
    + grid[[row |-> c.row - 1, col |-> c.col]]
    + grid[[row |-> c.row - 1, col |-> c.col - 1]]
    + grid[[row |-> c.row - 1, col |-> c.col + 1]]

TypeOK == grid \in [Cells -> BOOLEAN]

Init ==
  \E g \in [Cells -> BOOLEAN] :
    /\ grid = g

\* The fully deterministic, simultaneous update: the next value of every cell
\* depends only on the current generation's neighbor counts.
Tick ==
  LET g' == [c \in Cells |->
        IF grid[c]
          THEN IF Ones(c) \in {2, 3} THEN TRUE ELSE FALSE
          ELSE IF Ones(c) = 3 THEN TRUE ELSE FALSE]
  IN /\ grid' = g'

Next == Tick

Spec == Init /\ [][Next]_grid

\* The total set of live cells is fixed by the initial configuration and the
\* deterministic rule, so it can never drift away from its initially reachable
\* range: the system explores no state outside the set of generations
\* reachable from the chosen initial configuration.
StateSpace == {~(grid) : grid \in [Cells -> BOOLEAN]}
====