---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES alive
vars == <<alive>>

Neighbors == {<<dx, dy>> \in (-1..1) \X (-1..1) : ~(dx = 0 /\ dy = 0)}

\* Count live neighbors of position (i, j), treating positions outside the
\* N-by-N grid as dead (value zero).
LiveNeighbors(i, j) ==
  Cardinality({<<dx, dy>> \in Neighbors :
    LET x == i + dx
        y == j + dy
    IN x \in 1..N /\ y \in 1..N /\ alive[<<x, y>>]})

TypeOK ==
  /\ alive \in [1..N \X 1..N -> BOOLEAN]

Init ==
  /\ alive \in [1..N \X 1..N -> BOOLEAN]

Tick ==
  /\ alive' = [c \in 1..N \X 1..N |->
        LET n == LiveNeighbors(c[1], c[2])
        IN IF alive[c] /\ n \in {2, 3} THEN TRUE
           ELSE IF ~alive[c] /\ n = 3 THEN TRUE
           ELSE FALSE]
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====