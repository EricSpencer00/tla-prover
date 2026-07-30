---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

\* Conway's Game of Life: a deterministic, fully-synchronous cellular automaton
\* on a bounded square grid. Every cell updates at once, and each update is
\* determined entirely by the current population of its eight neighboring cells.
\* The grid has fixed boundaries; positions outside the grid are treated as
\* permanently dead and contribute nothing to neighbor counts.

CONSTANT N

Cells == {c \in 1..N : TRUE}
Neighbours == {n \in 1..N : TRUE}

VARIABLES state
vars == <<state>>

TypeOK == state \in [Cells -> BOOLEAN]

\* Count the number of live cells among the eight immediate neighbors of a cell
\* at position (x, y). Positions that fall outside the grid count as dead.
NeighborsOf(x, y) ==
  LET
    values == {IF i \in Cells /\ j \in Cells THEN state[i, j] ELSE FALSE
                 : i \in {x - 1, x, x + 1}, j \in {y - 1, y, y + 1}}
    deltas == {v \in values : v = TRUE}
  IN Cardinality(deltas)

Init == state \in [Cells -> BOOLEAN]

\* Simultaneous update: every cell is rewritten in the same step using the
\* neighbor counts computed from the current state alone. This is what makes
\* the automaton deterministic -- the entire next generation is fixed once
\* the current one is fixed.
Tick ==
  \E newState \in [Cells -> BOOLEAN] :
    /\ \A x \in Cells, y \in Cells :
         LET n == NeighborsOf(x, y) IN
           newState[x, y] = (IF state[x, y] THEN (n = 2 \/ n = 3) ELSE (n = 3))
    /\ state' = newState

Next == Tick

Spec == Init /\ [][Next]_vars

====