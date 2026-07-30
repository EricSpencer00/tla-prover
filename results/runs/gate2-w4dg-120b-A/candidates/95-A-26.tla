---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == (1 .. N) \X (1 .. N)
Neighbors == (-1 .. 1) \X (-1 .. 1)

VARIABLES grid

vars == <<grid>>

RECURSIVE SumOverRows(_, _)
SumOverRows(f, y) ==
  IF y = 0 THEN 0
  ELSE f[y] + SumOverRows(f, y - 1)

RECURSIVE SumPairs(_, _, _)
SumPairs(f, rows, cols) ==
  IF rows = 0 THEN 0
  ELSE SumOverRows([c \in 1 .. cols |-> f[rows, c]], cols) + SumPairs(f, rows - 1, cols)

AliveNeighbors(p) ==
  LET add(a, b) == a + b
  IN SumPairs([r \in 1 .. N, c \in 1 .. N |-> IF p[1] + r \in 1 .. N /\ p[2] + c \in 1 .. N /\ (r # 0 \/ c # 0)
                                          THEN IF grid[p[1] + r, p[2] + c] THEN 1 ELSE 0
                                          ELSE 0], N, N)

Init ==
  /\ grid \in [Cells -> BOOLEAN]

LiveRule(n) == n = 2 \/ n = 3
BirthRule(n) == n = 3

Tick ==
  /\ grid' = [p \in Cells |-> IF grid[p] THEN LiveRule(AliveNeighbors(p)) ELSE BirthRule(AliveNeighbors(p))]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ grid \in [Cells -> BOOLEAN]

====