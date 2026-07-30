---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* Grid positions range over the closed interval [1, N] for both rows and columns.
\* This avoids the "zero" index that some alternative encodings use.
Positions == (1 .. N) \X (1 .. N)

\* Two cells are orthogonal if they lie in the same row or the same column; otherwise
\* they are diagonal.  This is needed to compute the Chebyshev distance correctly.
Orthogonal(p, q) == p[1] = q[1] \/ p[2] = q[2]

\* The Chebyshev distance dist(p, q) is the number of steps a king needs to reach q
\* from p on a chessboard -- 0 for the same position, 1 for an orthogonal neighbor,
\* and 2 for a diagonal neighbor.  Because N >= 1, the distance is always at most 2,
\* so 2*dist + 1 is in the range 1..5 and the indexing below never goes out of bounds.
dist(p, q) == IF p = q THEN 0 ELSE IF Orthogonal(p, q) THEN 1 ELSE 2

Neighbors(p) == { q \in Positions : dist(p, q) # 0 /\ 2 * dist(p, q) + 1 <= 5 }

VARIABLES alive

vars == <<alive>>

\* A live cell with exactly two or three live neighbors survives; a dead cell with
\* exactly three live neighbors becomes alive; everything else becomes dead.
NextAlive(p) == LET s == Cardinality({ q \in Neighbors(p) : alive[q] })
                 IN (alive[p] /\ (s = 2 \/ s = 3)) \/ (~alive[p] /\ s = 3)

TypeOK == /\ alive \in [Positions -> BOOLEAN]

Init == /\ alive \in [Positions -> BOOLEAN]
        /\ Cardinality(alive) >= 0

Tick == /\ alive' = [p \in Positions |-> NextAlive(p)]

Next == Tick

Spec == Init /\ [][Next]_vars

====