---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode the disks present as a bit-sum: bit k set <=> disk 2^k is there.
\* Conservation is enforced as a sum of all tower values equalling 2^D - 1.
\* Moves are legal iff the source's smallest disk is the one moved and the destination
\* has no smaller disk already present -- the classic Hanoi size ordering.
\* Nondeterministic moves explore every valid solution; there is no liveness claim.

VARIABLES towers

vars == <<towers>>

OnTower(d, t) == towers[t] % (2 * d) >= d

SumOver(f, i, m) ==
    IF i > m THEN 0
    ELSE f[i] + SumOver(f, i + 1, m)

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D) - 1]
    /\ SumOver(towers, 1, N) = (2 ^ D) - 1

Init ==
    /\ towers = [t \in 1..N |-> IF t = 1 THEN (2 ^ D) - 1 ELSE 0]

Move(d, src, dst) ==
    /\ src # dst
    /\ OnTower(d, src)
    /\ \A k \in 1..D : IF k < d THEN ~OnTower(k, src) ELSE TRUE
    /\ \A k \in 1..D : k < d => ~OnTower(k, dst)
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \/ \E src, dst \in 1..N : Move(1, src, dst)
    \/ \E src, dst \in 1..N : Move(2, src, dst)
    \/ \E src, dst \in 1..N : Move(4, src, dst)
    \/ \E src, dst \in 1..N : Move(8, src, dst)

Spec == Init /\ [][Next]_vars

Inv == TypeOK
====