---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

Rows == 1..N
Cols == 1..N
Positions == Rows \X Cols

VARIABLES grid

vars == <<grid>>

Neighbors == <<-1, -1>, <<-1, 0>, <<-1, 1>,
               <<0, -1>>,           <<0, 1>>,
               <<1, -1>,  <<1, 0>>, <<1, 1>>


Within(r, c) == r \in Rows /\ c \in Cols

\* The environment treats all cells outside the grid as dead.
CellValueAt(r, c) == IF Within(r, c) THEN grid[r, c] ELSE FALSE

\* Count live neighbors around the cell at (r, c) by enumerating
\* the eight possible neighbor offsets and folding in the cell's value.
NeighborCount(r, c) ==
  LET f[S \in SUBSET Positions] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
                 dr == x[1]
                 dc == x[2]
                 rest == S \ {x}
                 rr == r + dr
                 cc == c + dc
                 alive == IF CellValueAt(rr, cc) THEN 1 ELSE 0
             IN alive + f[rest]
  IN f[Neighbors]

TypeOK == grid \in [Positions -> BOOLEAN]

InitGrid ==
  [p \in Positions |-> IF Cardinality({q \in Positions : q = p}) = 1
                        THEN (CHOOSE b \in BOOLEAN : TRUE)
                        ELSE FALSE]

\* Simultaneous deterministic update: the next state of every cell is
\* computed from the current state, so the whole grid moves as one.
NextState(r, c) ==
  LET n == NeighborCount(r, c) IN
    IF grid[r, c] THEN n = 2 \/ n = 3
    ELSE n = 3

Tick ==
  /\ grid' = [p \in Positions |-> NextState(p[1], p[2])]
  /\ UNCHANGED << >>

Next ==
  \/ Tick
  \/ UNCHANGED <<grid>>

Spec == Init /\ [][Next]_vars

Init == grid = InitGrid

====