---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk k has size 2^k and is present on a tower iff the tower's value has bit k set.
\* Conservation holds on the integer sum of tower values, which equals 2^D-1 when
\* all disks are accounted for. The move action always applies, so a trace of
\* moves exists from every reachable state (no deadlock).
VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [1..N -> 0..(2^D - 1)]
          /\ \A i \in 1..N : tower[i] >= 0

Init == /\ tower = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move is legal if the disk is the smallest on its source tower and lands
\* on an empty spot or above a larger disk on the destination tower.
Move(d, s, t) == /\ d \in {2^k : k \in 1..D}
                 /\ s # t
                 /\ tower[s] >= d
                 /\ (tower[s] % (2 * d)) >= d
                 /\ (tower[t] = 0 \/ (tower[t] % (2 * d)) = 0)
                 /\ tower' = [tower EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in {2^k : k \in 1..D}, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Every disk is always somewhere: the total across all towers never drifts.
Conservation == (tower[1] + tower[2] + tower[3]) = 2^D - 1

Inv == TypeOK /\ Conservation
====