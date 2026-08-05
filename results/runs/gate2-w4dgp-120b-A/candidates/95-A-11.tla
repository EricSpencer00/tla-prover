---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Cells == UNION {[i \in 1..N, j \in 1..N] : {}}

InitCell == CHOOSE c \in Cells : TRUE

\* neighborCount(p): number of live neighbors of cell p, counting cells
\* outside the grid as dead (value zero). p lives in 1..N x 1..N, so p.i +/- 1
\* and p.j +/- 1 stay within the Nat universe; membership in Cells filters
\* out-of-grid positions (treating them as dead) without any extra bounds check.
neighborCount(p) ==
  LET c(i, j) == IF <<i, j>> \in Cells THEN alive[<<i, j>>] ELSE FALSE IN
    (IF c(p.i-1, p.j-1) THEN 1 ELSE 0)
    + (IF c(p.i-1, p.j) THEN 1 ELSE 0)
    + (IF c(p.i-1, p.j+1) THEN 1 ELSE 0)
    + (IF c(p.i, p.j-1) THEN 1 ELSE 0)
    + (IF c(p.i, p.j+1) THEN 1 ELSE 0)
    + (IF c(p.i+1, p.j-1) THEN 1 ELSE 0)
    + (IF c(p.i+1, p.j) THEN 1 ELSE 0)
    + (IF c(p.i+1, p.j+1) THEN 1 ELSE 0)

TypeOK ==
  /\ alive \in [Cells -> BOOLEAN]

Init ==
  /\ \E f \in [Cells -> BOOLEAN] : alive = f

\* Tick: every cell updates simultaneously from the same source generation.
\* The rule is deterministic (survival with 2 or 3 neighbors, birth at exactly 3),
\* so a given initial configuration yields exactly one evolution.
Tick ==
  /\ alive' = [p \in Cells |-> (alive[p] /\ (neighborCount(p) = 2 \/ neighborCount(p) = 3))
                              \/ (~alive[p] /\ neighborCount(p) = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

====