---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

RECURSIVE SumOver(_, _)
SumOver(f, k) ==
    IF k = 0 THEN 0
    ELSE f[k] + SumOver(f, k - 1)

Masked(v, d) == (v \div d) % 2

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]

Init ==
    /\ towers = [t \in 1..N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]

Move(d, src, dst) ==
    /\ src # dst
    /\ d \in 1..(2 ^ (D - 1))
    /\ towers[src] >= d
    /\ Masked(towers[src], d) = 1
    /\ \A e \in 1..(d - 1) : Masked(towers[src], e) = 0
    /\ \A e \in 1..(d - 1) : Masked(towers[dst], e) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \/ \E d \in 1..(2 ^ (D - 1)), src \in 1..N, dst \in 1..N : Move(d, src, dst)

Inv ==
    /\ SumOver(towers, N) = 2 ^ D - 1
    /\ TypeOK

Spec == Init /\ [][Next]_vars

====