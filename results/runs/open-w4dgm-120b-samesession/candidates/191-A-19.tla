---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower i holds the sum of disk values (powers of two) currently on it.
VARIABLES towers

vars == <<towers>>

\* Bitwise AND via a recursive arithmetic definition; applied to naturals.
BitAnd(x, y) == IF y = 0 THEN 0 ELSE
    LET b == y % 2 IN (IF (x % 2) * b = 1 THEN 1 ELSE 0) + 2 * BitAnd(x \div 2, y \div 2)

\* Sum of a sequence of tower values (total disk mass).
SumTowers(i) == IF i = 0 THEN 0 ELSE towers[i] + SumTowers(i - 1)

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]
    /\ SumTowers(N) = 2 ^ D - 1

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

\* A move is legal only if the disk is on the source, is the smallest there,
\* and the destination has no smaller disk underneath it.
Move(d, from, to) ==
    /\ d \in {2 ^ k : k \in 1..D}
    /\ from # to
    /\ towers[from] >= d
    /\ BitAnd(towers[from], d) = 1
    /\ (towers[from] \div (2 * d)) * (2 * d) = towers[from] - d
    /\ (towers[to] = 0 \/ (towers[to] \div (2 * d)) * (2 * d) = towers[to])
    /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next == \E d \in {2 ^ k : k \in 1..D}, from \in 1..N, to \in 1..N: Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: no disk is ever created or destroyed.
Inv == SumTowers(N) = 2 ^ D - 1

====