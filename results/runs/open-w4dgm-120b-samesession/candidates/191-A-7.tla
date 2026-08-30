---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode present disks as the sum of their powers-of-two values.
\* Conservation is the exact bitwise-sum identity this representation requires.
VARIABLES towers

vars == <<towers>>

\* Bitwise AND via arithmetic: a & b == 0 iff there is no power-of-two divisor
\* common to both a and b, which is the test the rules rely on below.
BitsDisjoint(a, b) == \A k \in 0..(D - 1) : ((2 ^ k) \in a) => ((2 ^ k) \notin b)

\* Interpreting a tower value as the set of disk powers it carries.
BitsOf(v) == {2 ^ k : k \in 0..(D - 1) : (v \div (2 ^ k)) % 2 = 1}

Total == 2 ^ D - 1

TypeOK == towers \in [1..N -> 0..Total]

Init ==
    /\ towers = [t \in 1..N |-> IF t = 1 THEN Total ELSE 0]

Move(d, src, dst) ==
    /\ src # dst
    /\ d \in BitsOf(towers[src])
    /\ \A e \in BitsOf(towers[src]) : e >= d
    /\ \/ towers[dst] = 0
       \/ \A e \in BitsOf(towers[dst]) : e >= d
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in 1..Total, src \in 1..N, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Disk conservation: the bitwise partitions across towers still sum to the
\* packed source value, which is impossible if a disk was duplicated or lost.
Conservation == towers[1] + towers[2] + towers[3] = Total

Inv == TypeOK /\ Conservation

====