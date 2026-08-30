---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES grid

vars == <<grid>>

Cell == {1..N} \X {1..N}

\* Each cell holds a boolean (TRUE = alive, FALSE = dead); cells outside the
\* N-by-N bounds are treated as permanently dead (value FALSE) for neighbor counts.
Neighbors(c) ==
  { <<r2, c2>> :
      LET dr == r2 - c[1]
          dc == c2 - c[2]
      IN dr \in -1..1 /\ dc \in -1..1 /\ (dr # 0 \/ dc # 0)
         /\ r2 \in 1..N /\ c2 \in 1..N }

\* Live-neighbor count for a cell; out-of-bounds to a dead value FALSE.
LiveCount(c) ==
  Cardinality({n \in Neighbors(c) : grid[n]})

TypeOK == grid \in [Cell -> BOOLEAN]

\* Every live cell with 2 or 3 live neighbors survives; every dead cell with exactly
\* 3 live neighbors becomes alive; all other cells die -- applied to the whole grid
\* simultaneously, which is what makes the step deterministic.
Init ==
  /\ \E g \in [Cell -> BOOLEAN] : grid = g
  /\ UNCHANGED <<>>

Tick ==
  /\ grid' = [c \in Cell |-> IF (grid[c] /\ LiveCount(c) \in {2, 3})
                            \/ (~grid[c] /\ LiveCount(c) = 3)
                              THEN TRUE ELSE FALSE]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

\* No hidden dimension or hidden domain: every grid entry is always a boolean.
GridBoolean == TypeOK

====