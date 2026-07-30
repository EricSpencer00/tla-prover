---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

VARIABLES cell
vars == <<cell>>

Positions == {p \in (1..N) \X (1..N)}

RECURSIVE CountAlive(_)
CountAlive(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN (IF cell[x] THEN 1 ELSE 0) + CountAlive(S \ {x})

Neighbors(p) == {[p[1] + dr, p[2] + dc] \in Positions : dr \in {-1, 0, 1}, dc \in {-1, 0, 1}, ~(dr = 0 /\ dc = 0)}

TypeOK ==
    /\ cell \in [Positions -> BOOLEAN]

Init ==
    /\ cell \in [Positions -> BOOLEAN]

Tick ==
    /\ cell' = [p \in Positions |-> LET alive == cell[p] IN LET cnt == CountAlive(Neighbors(p)) IN IF alive /\ (cnt = 2 \/ cnt = 3) THEN TRUE ELSE IF ~alive /\ cnt = 3 THEN TRUE ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_vars

====