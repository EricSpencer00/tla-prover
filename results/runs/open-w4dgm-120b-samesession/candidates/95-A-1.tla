---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Positions == 1..N

Neighbors == {dx \in {-1, 1}, dy \in {-1, 1}} \cup
             {dx \in {-1, 1}, dy \in {0}} \cup
             {dx \in {0}, dy \in {-1, 1}}

\* A neighbor lies outside the grid: it is treated as dead (value zero).
InGrid(r, c) == r \in Positions /\ c \in Positions

\* A cell's live-neighbor count is summed over the eight surrounding positions.
LiveNeighbors(r, c) ==
    LET neighborAlive(p, q) ==
        IF InGrid(p, q) THEN IF alive[p, q] THEN 1 ELSE 0 ELSE 0
    IN  LET deltas == {{dx, dy} : dx \in {-1, 0, 1}, dy \in {-1, 0, 1}, ~(dx = 0 /\ dy = 0)}
        IN  LET contributions == {neighborAlive(r + deltas[i][1], c + deltas[i][2])
                                  : i \in 1..Cardinality(deltas)}
            IN  LET add[T \in SUBSET (0..Cardinality(deltas))] ==
                    IF T = {} THEN 0
                    ELSE LET x == CHOOSE y \in T : TRUE
                         IN  contributions[x] + add[T \ {x}]
                IN  add[1..Cardinality(deltas)]

TypeOK ==
    /\ alive \in [Positions \X Positions -> BOOLEAN]

Init ==
    \E f \in [Positions \X Positions -> BOOLEAN] : alive = f

\* Fully deterministic synchronous update: given the current grid, the next
\* generation is unique, so no nondeterministic choice remains here.
Tick ==
    /\ LET f' == [p \in Positions \X Positions |->
                    LET cnt == LiveNeighbors(p[1], p[2])
                    IN  IF alive[p] THEN cnt \in {2, 3} ELSE cnt = 3]
       IN  alive' = f'
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

\* The grid's representation always stays Boolean-valued per cell, which is
\* what the fully deterministic update depends on for its own determinism.
BoundedTypeOK == TypeOK

====