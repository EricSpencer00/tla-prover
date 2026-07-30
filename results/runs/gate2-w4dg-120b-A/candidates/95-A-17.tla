---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

VARIABLES grid

vars == <<grid>>

Cells == [1..N, 1..N]

Neighbors == 8

\* Count the live neighbors of a cell, treating any position outside the
\* grid as dead (value zero) as the description requires.
NeighborsAlive(c) ==
  LET count(p) == IF p \in Cells THEN IF grid[p] THEN 1 ELSE 0 ELSE 0
      offsets == {[-1 .. 1], [-1 .. 1]} \ {{0, 0}}
  IN  Cardinality({o \in offsets : count([c[1] + o[1], c[2] + o[2]]) = 1})

Survives(c) ==
  \E k \in {2, 3} : NeighborsAlive(c) = k

Reproduces(c) ==
  NeighborsAlive(c) = 3

\* The update is deterministic: given the current grid, the next grid is
\* uniquely fixed.  The description calls the action "simultaneous update"
\* and this is exactly one step of the automaton.
Tick ==
  /\ grid' = [c \in Cells |-> Survives(c) \/ Reproduces(c)]
  /\ UNCHANGED <<>>

Init ==
  /\ grid \in [Cells -> BOOLEAN]
  /\ UNCHANGED <<>>

Spec == Init /\ [][Tick]_vars

TypeOK == grid \in [Cells -> BOOLEAN]

====