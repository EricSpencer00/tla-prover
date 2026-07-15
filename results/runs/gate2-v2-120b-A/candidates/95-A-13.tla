---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

\* The set of all valid grid positions (1..N, 1..N)
Pos == 1..N

\* State variable: a function mapping each position to a Boolean (TRUE = alive, FALSE = dead)
VARIABLE grid

\* Helper to count live neighbors of a given position (treating out‑of‑bounds as dead)
Neighbors(p) ==
  LET row == p[1];
      col == p[2];
      deltas == {{-1, -1}, {-1, 0}, {-1, 1},
                 { 0, -1},          { 0, 1},
                 { 1, -1}, { 1, 0}, { 1, 1}} IN
  { <<row + dr, col + dc>> :
       <<dr, dc>> \in deltas /\ 
       row + dr \in Pos /\ col + dc \in Pos }

LiveNeighborCount(p) == Cardinality({ q \in Neighbors(p) : grid[q] })

\* Deterministic update rule for a single cell
UpdateCell(p) ==
  LET cnt == LiveNeighborCount(p) IN
  IF grid[p] THEN  (* cell currently alive *)
    cnt = 2 \/ cnt = 3
  ELSE               (* cell currently dead *)
    cnt = 3

\* Initial state: each cell nondeterministically alive or dead
Init == 
  /\ grid \in [Pos -> BOOLEAN]

\* Tick action: simultaneous update of all cells
Tick ==
  /\ grid' = [p \in Pos |-> UpdateCell(p)]

\* Stuttering step to avoid deadlock when N = 0 (not reachable under normal usage)
Stutter == UNCHANGED grid

Next == Tick \/ Stutter

\* Full behavior specification
Spec == Init /\ [][Next]_<<grid>>

\* Type correctness invariant
TypeOK == grid \in [Pos -> BOOLEAN]

\* The name expected by the .cfg file for the whole spec
Spec == Init /\ [][Next]_<<grid>>

====