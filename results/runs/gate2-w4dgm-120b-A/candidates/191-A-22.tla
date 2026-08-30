---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk i has size 2^i and is encoded as the i-th bit of a tower's value.
Disk(i) == 2 ^ i
AllDisks == 2 ^ D - 1

\* Bitwise AND via arithmetic: no remainder when dividing by the sum of the
\* two operands' lowest set bits means they share no 1-bit.
BitwiseAnd(x, y) == IF x = 0 \/ y = 0 THEN 0
                    ELSE LET lx == 2 ^ (x % 2)
                             ly == 2 ^ (y % 2)
                         IN IF (lx + ly) > x + y
                            THEN 0
                            ELSE lx + ly + BitwiseAnd(x \div 2, y \div 2)

VARIABLES towers
vars == <<towers>>

TypeOK ==
    /\ towers \in [1..N -> 0..AllDisks]
    /\ \A i \in 1..N : towers[i] >= 0 /\ towers[i] <= AllDisks

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

Move(d, source, dest) ==
    /\ d \in 1..D
    /\ source \in 1..N
    /\ dest \in 1..N
    /\ source # dest
    /\ towers[source] # 0
    /\ towers[dest] <= AllDisks
    /\ BitwiseAnd(towers[source], Disk(d)) = Disk(d)
    /\ BitwiseAnd(towers[source] \div Disk(d), Disk(d) - 1) = 0
    /\ \/ towers[dest] = 0
       \/ BitwiseAnd(towers[dest], Disk(d) - 1) = 0
    /\ towers' = [towers EXCEPT ![source] = @ - Disk(d), ![dest] = @ + Disk(d)]

Next == \E d \in 1..D, source \in 1..N, dest \in 1..N : Move(d, source, dest)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise representation is a lossless encoding of all disks.
Conserved == towers[1] + towers[2] + (IF N > 2 THEN towers[3] ELSE 0)
             + (IF N > 3 THEN towers[4] ELSE 0)
             + (IF N > 4 THEN towers[5] ELSE 0) = AllDisks

Inv == TypeOK /\ Conserved
====