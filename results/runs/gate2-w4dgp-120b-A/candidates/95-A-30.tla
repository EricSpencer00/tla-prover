---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cells
vars == <<cells>>

Rows == 0..(N-1)
Cols == 0..(N-1)
Positions == Rows \X Cols
Neighbors == {(-1)..1} \X {(-1)..1}

TypeOK ==
    /\ cells \in [Positions -> BOOLEAN]

Init ==
    /\ cells = [p \in Positions |-> CHOOSE v \in BOOLEAN : TRUE]

\* Count the live neighbors of position p, treating positions outside the grid
\* (which are not in Positions) as dead.
SumAlive(p) ==
    LET f(S) ==
        IF S = {} THEN 0
        ELSE LET q == CHOOSE x \in S : TRUE
                 rel == IF q \in Neighbors THEN q ELSE <0, 0>
                 neighborPos == <<p[1] + rel[1], p[2] + rel[2]>>
                 delta == IF neighborPos \in Positions /\ cells[neighborPos] THEN 1 ELSE 0
             IN delta + f(S \ {q})
    IN f(Neighbors)

\* One generation: every cell computes its next state from the same current
\* snapshot, so the update is truly simultaneous.
Tick ==
    /\ cells' = [p \in Positions |->
                    LET n == SumAlive(p)
                    IN IF cells[p] THEN n = 2 \/ n = 3
                       ELSE n = 3]
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====