---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == [1 .. N] \X [1 .. N]

Neighbors == {dr, dc \in {1, 2, 3}}
                : (dr, dc) # (2, 2)

VARIABLES alive

vars == <<alive>>

TypeOK ==
  /\ alive \in [Cells -> BOOLEAN]

\* Each cell has up to eight neighbours.  Cells outside the grid boundaries
\* are treated as dead (value zero) when counting live neighbours.
LiveNeighbors(c) ==
  Cardinality({n \in Cells :
                 /\ \E dr \in {1, 2, 3}, dc \in {1, 2, 3} :
                      dr # dc /\ n = <<c[1] + dr - 2, c[2] + dc - 2>>
                 /\ alive[n]})

Init ==
  /\ alive \in [Cells -> BOOLEAN]

\* Fully deterministic simultaneous update: each generation follows uniquely
\* from the previous one once the initial configuration is fixed.
Tick ==
  /\ \E alive' \in [Cells -> BOOLEAN] :
       /\ \A c \in Cells :
            alive'[c] =
              \/ /\ alive[c] /\ LiveNeighbors(c) \in {2, 3}
                 /\ TRUE
              \/ /\ ~alive[c] /\ LiveNeighbors(c) = 3
                 /\ TRUE
       /\ UNCHANGED alive
  /\ alive' \in [Cells -> BOOLEAN]

Next == Tick

Spec == Init /\ [][Next]_vars

====