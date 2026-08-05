---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == 0..(N - 1)
Grid == Cells \X Cells

VARIABLES alive

TypeOK ==
    /\ alive \in [Grid -> BOOLEAN]

Neighbors(r, c) ==
    { <<rr, cc>> \in Grid :
        /\ Abs(rr - r) <= 1
        /\ Abs(cc - c) <= 1
        /\ ~(rr = r /\ cc = c)
    }

LiveNeighbors(r, c) ==
    Cardinality({p \in Neighbors(r, c) : alive[p]})

Init ==
    /\ alive = [p \in Grid |-> CHOOSE b \in BOOLEAN : TRUE]

Tick ==
    /\ alive' = [p \in Grid |->
        LET ln == LiveNeighbors(p[1], p[2]) IN
        IF alive[p] THEN ln \in {2, 3} ELSE ln = 3
    ]

Next == Tick

Spec == Init /\ [][Next]_alive

====