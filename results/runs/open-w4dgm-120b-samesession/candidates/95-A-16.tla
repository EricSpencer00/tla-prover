---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

Positions == (1 .. N) \X (1 .. N)

Neighbors(p) == {
    <<q[1] + dr, q[2] + dc>> :
        dr \in {-1, 0, 1}, dc \in {-1, 0, 1},
        ~(dr = 0 /\ dc = 0),
        LET q == p IN TRUE
}

VARIABLES cell
vars == <<cell>>

\* A cell outside the grid boundary is treated as dead (value zero) for neighbor
\* counting, so every cell always has exactly eight neighbor slots to consider.
NeighborSum(p) ==
    LET sum[S \in SUBSET Positions] ==
        IF S = {} THEN 0
        ELSE LET q == CHOOSE x \in S : TRUE IN cell[q] + sum[S \ {q}]
    IN sum[Neighbors(p)]

TypeOK == cell \in [Positions -> BOOLEAN]

Init == \E f \in [Positions -> BOOLEAN] : cell = f

Tick ==
    /\ cell' = [p \in Positions |->
        IF cell[p] /\ NeighborSum(p) \in {2, 3} THEN TRUE
        ELSE IF ~cell[p] /\ NeighborSum(p) = 3 THEN TRUE
        ELSE FALSE]
    /\ UNCHANGED vars

Next == Tick

Spec == Init /\ [][Next]_vars

====