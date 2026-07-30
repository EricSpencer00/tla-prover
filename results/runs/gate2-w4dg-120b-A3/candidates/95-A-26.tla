---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

Cells == (1..N) \X (1..N)

VARIABLES grid

vars == <<grid>>

RECURSIVE CountAlive(_)
CountAlive(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN (IF grid[x] THEN 1 ELSE 0) + CountAlive(S \ {x})

Neighbors(p) ==
    { q \in Cells : Cardinality({r \in [1..2] : p[r] = q[r] \/ ABS(p[r] - q[r]) = 1}) \in {2, 3} }

TypeOK ==
    /\ N \in Nat /\ N >= 1
    /\ grid \in [Cells -> BOOLEAN]

Init ==
    /\ grid \in [Cells -> BOOLEAN]

Tick ==
    /\ grid' = [p \in Cells |->
                   LET alive == CountAlive(Neighbors(p))
                   IN IF grid[p] THEN alive = 2 \/ alive = 3 ELSE alive = 3]
    /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====