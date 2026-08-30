---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of disk values (powers of two); a set bit means that
\* disk is present on that tower. Conservation is a sum over all towers.
VARIABLES towers

vars == <<towers>>

\* Bitwise AND via arithmetic: a & b = a - ((a + b) \div 2)
And(a, b) == a - ((a + b) \div 2)

TypeOK ==
    /\ towers \in [1..N -> 0..(2^D - 1)]
    /\ towers[N] \in 0..(2^D - 1)

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move is legal only if the disk is the smallest on its source tower and
\* the destination tower has no smaller disk already present.
Move(d, src, dst) ==
    /\ d \in {2^k : k \in 0..(D - 1)}
    /\ src # dst
    /\ And(towers[src], d) = d
    /\ And(towers[src] - d, d) = 0
    /\ And(towers[dst], d) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \E d \in {2^k : k \in 0..(D - 1)} \E src \in 1..N \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every disk is accounted for exactly once across all towers.
Inv ==
    /\ \A i \in 1..N : towers[i] \in 0..(2^D - 1)
    /\ (towers[1] + towers[2] + towers[3]) = 2^D - 1

====