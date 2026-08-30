---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Disks == 1 << (1 .. D)

VARIABLES tower
vars == <<tower>>

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN tower[x] + SumOf(S \ {x})

AndBits(x, y) == x \in Disks /\ y \in Disks /\ (x >= y \/ x = y \/ x % (2 * y) = y)

TypeOK ==
    /\ tower \in [1 .. N -> 0 .. (1 << D) - 1]
    /\ \A t \in 1 .. N: tower[t] = 0 \/ tower[t] \in Disks

Init ==
    /\ tower = [t \in 1 .. N |-> IF t = 1 THEN (1 << D) - 1 ELSE 0]

Move(d, s, e) ==
    /\ d \in Disks
    /\ s # e
    /\ tower[s] >= d
    /\ AndBits(tower[s], d)
    /\ (tower[e] = 0 \/ AndBits(tower[e], d))
    /\ tower' = [tower EXCEPT ![s] = @ - d, ![e] = @ + d]

Next ==
    \E d \in Disks, s \in 1 .. N, e \in 1 .. N: Move(d, s, e)

Spec == Init /\ [][Next]_vars

Inv == SumOf(1 .. N) = (1 << D) - 1
====