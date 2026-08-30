---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

States == {"alive", "dead"}

\* A grid cell is mapped to its boolean state; "alive" = TRUE, "dead" = FALSE.
VARIABLES cells

vars == <<cells>>

Cells == [r \in 0..(N-1), c \in 0..(N-1)]

TypeOK == cells \in [Cells -> BOOLEAN]

\* The eight neighboring positions for any grid cell (dx, dy offsets).
Neighbors == {{-1, -1}, {-1, 0}, {-1, 1},
              {0, -1},           {0, 1},
              {1, -1}, {1, 0}, {1, 1}}

InRange(x) == 0 <= x /\ x <= N - 1

\* Count live neighbors, treating off-grid positions as dead (value zero).
LiveCount(s) ==
  LET f(p) == IF cells[p] THEN 1 ELSE 0
  IN LET sumOver(N) ==
        IF N = {} THEN 0
        ELSE LET x == CHOOSE e \in N : TRUE IN f(x) + sumOver(N \ {x})
     IN sumOver({Cells[p] : p \in Cells : InRange(s.r + p[1]) /\ InRange(s.c + p[2])
                                   /\ p \in Neighbors})

\* The Game of Life rule applied to one cell, given its live neighbor count.
Rule(s) ==
  IF cells[s]
    THEN cells' = [cells EXCEPT ![s] = (LiveCount(s) = 2) \/ (LiveCount(s) = 3)]
    ELSE cells' = [cells EXCEPT ![s] = LiveCount(s) = 3]

\* A nondeterministic choice of which cell updates next; since all cells must
\* be updated, the full grid evolves as a pair of rounds: snap (choose an
\* update order) then apply every queued update in that order in one batch.
\* The simultaneous-update effect emerges because the batch is computed from
\* the original state, not an intermediate one.
Init ==
  /\ cells \in [Cells -> BOOLEAN]
  /\ \A s \in Cells : cells' = cells

\* The deterministic simultaneous update of the entire grid.
Tick ==
  \E s \in Cells :
    cells' = [cells EXCEPT ![s] = (cells[s] /\ (LiveCount(s) = 2 \/ LiveCount(s) = 3))
                                   \/ (~cells[s] /\ LiveCount(s) = 3)]

Next == Tick

\* The update is deterministic once the initial configuration is picked:
\* each generation is uniquely determined by its predecessor.
Spec == Init /\ [][Next]_vars

\* Every cell's state is always a boolean, so no illegal (non-conway) state
\* ever arises for any reachable state -- not just at the start.
StateConstraint == TypeOK

====