---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Positions == {1..N} \X {1..N}

VARIABLES grid

vars == <<grid>>

\* The count of live neighbors for position p, summing values for the eight
\* surrounding cells and treating anything outside the grid as dead (zero).
RECURSIVE Neigh(_)
Neigh(S) ==
  IF S = {} THEN 0
  ELSE LET p == CHOOSE x \in S : TRUE
           deltas == {p[1] - 1, p[1], p[1] + 1} \X {p[2] - 1, p[2], p[2] + 1}
           deltas' == deltas \ {p}
           val == IF p \in Positions THEN grid[p] ELSE FALSE
       IN val + Neigh(deltas' \cup S)

TypeOK == grid \in [Positions -> BOOLEAN]

Init ==
  /\ grid \in [Positions -> BOOLEAN]

\* Every cell updates simultaneously based on the same neighbor counts.
Tick ==
  /\ grid' = [p \in Positions |-> IF grid[p]
                  THEN (Neigh({p}) = 2 \/ Neigh({p}) = 3)
                  ELSE (Neigh({p}) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====