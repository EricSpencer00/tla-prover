---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers
vars == <<towers>>

RECURSIVE SumTower(_)
SumTower(k) == IF k = 0 THEN 0
               ELSE towers[k] + SumTower(k - 1)

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D - 1) ELSE 0]

MoveDisk(d, src, dst) ==
    /\ d \in {2 ^ k : k \in 0..(D - 1)}
    /\ src # dst
    /\ (towers[src] /\ d) = d
    /\ (towers[src] % d = 0)
    /\ (towers[dst] = 0 \/ (towers[dst] % d = 0))
    /\ towers' = [towers EXCEPT ![src] = towers[src] - d, ![dst] = towers[dst] + d]

Next ==
    \/ \E d \in {2 ^ k : k \in 0..(D - 1)}, s \in 1..N, t \in 1..N : MoveDisk(d, s, t)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ SumTower(N) = (2 ^ D - 1)
    /\ TypeOK
====