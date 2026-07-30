---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode the set of disks present as a bit field: disk k has size
\* 2^k. All disks start on the first tower; none are created or destroyed.
Disks == { 2 ^ k : k \in 0 .. (D - 1) }
TowerVals == { 0 .. (2 ^ D) - 1 }

VARIABLES tower

vars == <<tower>>

\* Tower i's smallest disk is the least-order bit that is set; the move
\* constraint tests that a source tower carries nothing smaller than the disk
\* it is about to give up.
Smallest(t) == CHOOSE k \in 0 .. (D - 1) : ((tower[t] % (2 * (2 ^ k))) >= (2 ^ k))

TypeOK ==
    /\ tower \in [0 .. (N - 1) -> TowerVals]

Init ==
    /\ tower = [t \in 0 .. (N - 1) |-> IF t = 0 THEN (2 ^ D) - 1 ELSE 0]

Move(d, src, dst) ==
    /\ src # dst
    /\ (tower[src] & d) = d
    /\ (tower[src] % (2 * d)) < (2 * d)
    /\ \A x \in Disks : (x < d) => ((tower[dst] & x) = 0)
    /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next ==
    \/ \E d \in Disks, src \in 0 .. (N - 1), dst \in 0 .. (N - 1) : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the bit fields always add back up to the full stack.
Inv ==
    /\ tower[0] + tower[1] + tower[2] = (2 ^ D) - 1
    /\ TypeOK
====