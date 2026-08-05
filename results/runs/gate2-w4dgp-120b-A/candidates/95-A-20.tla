---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == 1..N
Positions == Cells \X Cells

\* The value at a virtual neighbor position off the grid is treated as dead (zero).
Zero == [p \in Positions |-> FALSE]

VARIABLES alive

vars == <<alive>>

TypeOK ==
    /\ alive \in [Positions -> BOOLEAN]

Init ==
    /\ \E a \in [Positions -> BOOLEAN] : alive = a

\* A cell's live-neighbor count counts grid cells; positions outside the grid count as 0.
LiveNeighbors(p) ==
    LET dr == {-1, 0, 1}, dc == {-1, 0, 1} IN
        Cardinality({q \in Positions :
                        q # p /\ q \in dr \X dc /\ alive[q]})

\* The automaton updates every cell in lockstep based on the current configuration.
Tick ==
    /\ \E na \in [Positions -> BOOLEAN] :
        na = [p \in Positions |->
                IF alive[p] /\ (LiveNeighbors(p) = 2 \/ LiveNeighbors(p) = 3)
                THEN TRUE
                ELSE IF ~alive[p] /\ LiveNeighbors(p) = 3
                     THEN TRUE
                     ELSE FALSE]
    /\ alive' = na
    /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_vars

====