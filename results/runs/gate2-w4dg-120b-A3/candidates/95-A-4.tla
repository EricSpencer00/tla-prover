---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

Cells == 1..N

Positions == [r: Cells, c: Cells]

RECURSIVE CountLive(_)
CountLive(S) ==
    IF S = {} THEN 0
    ELSE LET p == CHOOSE e \in S : TRUE
         IN (IF grid[p] THEN 1 ELSE 0) + CountLive(S \ {p})

Neighbors(p) ==
    {q \in Positions :
        q # p /\ q.r \in p.r - 1 .. p.r + 1 /\ q.c \in p.c - 1 .. p.c + 1}

TypeOK ==
    /\ grid \in [Positions -> BOOLEAN]
    /\ N \in Nat

Init ==
    /\ grid \in [Positions -> BOOLEAN]
    /\ N \in Nat
    /\ N > 0

Tick ==
    /\ grid' = [p \in Positions |-> (grid[p] \/ (CountLive(Neighbors(p)) = 3))
                                        /\ (~grid[p] \/ (CountLive(Neighbors(p)) \in {2, 3}))]
    /\ UNCHANGED N

Next == Tick

Spec == Init /\ [][Next]_<<grid, N>>

====