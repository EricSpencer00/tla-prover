---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANT N

VARIABLES cell
vars == <<cell>>

Positions == 1..N

Neighbors == {
    <<dr, dc>> \in Cardinality([1..2], [1..2]) : dr # 0 \/ dc # 0
}

TypeOK ==
    /\ cell \in [Positions \X Positions -> BOOLEAN]

Init ==
    /\ cell \in [Positions \X Positions -> BOOLEAN]

AliveNeighbors(p) ==
    Cardinality({q \in Positions \X Positions : q # p /\ cell[q] /\ q \in {<<p[1] + dr, p[2] + dc>> : <<dr, dc>> \in Neighbors}})
                        \cap (Positions \X Positions)

Tick ==
    /\ cell' = [p \in Positions \X Positions |->
                    LET k == AliveNeighbors(p)
                    IN IF cell[p] THEN k = 2 \/ k = 3 ELSE k = 3]
    /\ UNCHANGED <<>>

Spec == Init /\ [][Tick]_vars

====