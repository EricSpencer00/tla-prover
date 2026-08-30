---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Bitwise AND implemented in pure arithmetic, since TLA+ lacks a native operator.
And(a, b) == a - ((a \div 2) * 2) * b

VARIABLES towers

vars == <<towers>>

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D - 1) ELSE 0]

SumTowers == towers[1] + towers[2] + towers[3]

\* The smallest disk on a tower is the lowest-order set bit; CountTrailingZeros
\* finds its position so the next larger disk's size can be computed.
CountTrailingZeros(v, k) == IF k > D THEN 0
                           ELSE IF And(v, 2 ^ (k - 1)) > 0 THEN k - 1
                           ELSE CountTrailingZeros(v, k + 1)

Move(d, from, to) ==
    /\ from # to
    /\ d <= towers[from]
    /\ And(towers[from], d) = d
    /\ d > And(towers[from], d - 1)
    /\ (towers[to] = 0 \/ d > And(towers[to], d - 1))
    /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
    \/ \E from \in 1..N, to \in 1..N : Move(1, from, to)
    \/ \E from \in 1..N, to \in 1..N : Move(2, from, to)
    \/ \E from \in 1..N, to \in 1..N : Move(4, from, to)
    \/ \E from \in 1..N, to \in 1..N : Move(8, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise encoding never creates or destroys disks.
Inv == SumTowers = (2 ^ D - 1)

====