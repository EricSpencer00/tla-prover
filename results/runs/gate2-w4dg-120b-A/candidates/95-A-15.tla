---- MODULE GameOfLife ----
EXTENDS Integers, FiniteSets

CONSTANTS N

Cell == [row: 1 .. N, col: 1 .. N]

VARIABLES alive

vars == <<alive>>

TypeOK == alive \in [Cell -> BOOLEAN]

\* A cell is within the grid iff its row and col both lie in the range 1..N,
\* so cells outside the grid (which are not in Cell) do not exist in the
\* state at all.  The Get function below treats any such out-of-range cell
\* as dead when counting neighbors.
InRange(c) == (c \in Cell)

\* Get returns the cell's value if it is inside the grid, or FALSE (dead)
\* for any position outside the grid boundaries.
Get(c) == IF InRange(c) THEN alive[c] ELSE FALSE

Neighbors(c) ==
  {[row |-> c.row + dr, col |-> c.col + dc] : dr \in {-1, 0, 1}, dc \in {-1, 0, 1}, (dr # 0 \/ dc # 0)}

AliveNeighbors(c) == Cardinality({n \in Neighbors(c) : Get(n)})

Init ==
  /\ alive \in [Cell -> BOOLEAN]

\* Simultaneous, deterministic update: each cell's next value depends only on
\* the current state, never on any other cell's new value.
Tick ==
  /\ alive' = [c \in Cell |-> LET k == AliveNeighbors(c) IN
                                      IF alive[c] /\ (k = 2 \/ k = 3) THEN TRUE
                                      ELSE IF ~alive[c] /\ k = 3 THEN TRUE
                                      ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====