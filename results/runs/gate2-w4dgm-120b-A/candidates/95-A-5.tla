---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* A cell is identified by its row and column within the N-by-N grid.
Cell == {p \in Nat \X Nat : p[1] \in 1..N /\ p[2] \in 1..N}

VARIABLES alive

vars == <<alive>>

\* The eight relative positions of a cell's neighbors; positions outside the
\* grid are treated as dead (contribute nothing) when counting.
Neighbors == {<<-1, -1>>, <<-1, 0>>, <<-1, 1>>, <<0, -1>>, <<0, 1>>, <<1, -1>>, <<1, 0>>, <<1, 1>>}

\* How many of a cell's eight neighbors are currently alive.
NumLiveNeighbors(p) ==
  Cardinality({n \in Neighbors : ((p[1] + n[1]) \in 1..N /\ (p[2] + n[2]) \in 1..N) /\ alive[p[1] + n[1], p[2] + n[2]]})

TypeOK == alive \in [Cell -> BOOLEAN]

Init ==
  \E f \in [Cell -> BOOLEAN] : alive = f

\* Fully deterministic simultaneous update given the current grid state.
Tick ==
  alive' = [p \in Cell |-> IF alive[p] /\ NumLiveNeighbors(p) \in {2, 3}
                           THEN TRUE
                           ELSE IF ~alive[p] /\ NumLiveNeighbors(p) = 3
                           THEN TRUE
                           ELSE FALSE]

Spec == Init /\ [][Tick]_vars

\* Safety: the grid's alive/dead values stay strictly Boolean -- they are never
\* left in an undefined or partially updated state.
TypeOKInv == TypeOK
====