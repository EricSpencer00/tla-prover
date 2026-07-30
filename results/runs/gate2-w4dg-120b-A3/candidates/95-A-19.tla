---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

\* Conway's Game of Life on a bounded N-by-N grid. Grid cells are updated
\* simultaneously in Tick; neighbor counts treat out-of-bounds positions as dead.

CONSTANTS N

ASSUME N \in Nat /\ N >= 1

Cells == 1 .. N

Positions == [r \in Cells, c \in Cells]

VARIABLES alive

vars == <<alive>>

TypeOK == alive \in [Positions -> BOOLEAN]

\* Each cell has up to eight neighbors; out-of-bounds neighborhoods count zero.
RECURSIVE NeighborCount(_, _)
NeighborCount(f, p) ==
  LET Adjacent ==
        {q \in Positions : q # p /\ (q.r >= p.r - 1 /\ q.r <= p.r + 1) /\ (q.c >= p.c - 1 /\ q.c <= p.c + 1)}
  IN Cardinality({q \in Adjacent : f[q]})

Init ==
  /\ alive \in [Positions -> BOOLEAN]

Tick ==
  /\ alive' = [p \in Positions |->
                 LET n == NeighborCount(alive, p)
                 IN IF alive[p] /\ (n = 2 \/ n = 3) THEN TRUE
                    ELSE IF ~alive[p] /\ n = 3 THEN TRUE
                    ELSE FALSE]
  /\ UNCHANGED <<>>

Spec == Init /\ [][Tick]_vars

====