---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk k has size 2^k. Tower t's value is a bitmask: bit k set <=> disk k is there.
\* The bitwise AND below is pure arithmetic, so no Java override is required.
VARIABLES tower

vars == <<tower>>

\* Masks for each decision: the disk being moved, the bits below it, and everything
\* above it. Disk k exists iff k < D, which caps the arithmetic.
DiskMask(k) == 2 ^ k
BelowMask(k) == DiskMask(k) - 1
AllMask == 2 ^ D - 1

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
    /\ tower \in [1..N -> 0..AllMask]
    /\ SumOf(tower, 1..N) = AllMask

Init ==
    /\ tower = [t \in 1..N |-> IF t = 1 THEN AllMask ELSE 0]

\* Disk k moves from src to dst iff it is present on src, is the smallest on src
\* (no lower bits set there), and dst has no smaller disk (no lower bits set).
Move(k, src, dst) ==
    /\ src # dst
    /\ tower[src] >= DiskMask(k)
    /\ (tower[src] % DiskMask(k)) = 0
    /\ (tower[dst] % DiskMask(k)) = 0
    /\ tower' = [tower EXCEPT ![src] = @ - DiskMask(k), ![dst] = @ + DiskMask(k)]
    /\ UNCHANGED << >>

Next == \E k \in 0..(D - 1), src \in 1..N, dst \in 1..N : Move(k, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every disk is on exactly one tower, summed as a mask.
Inv ==
    /\ SumOf(tower, 1..N) = AllMask
    /\ \A t \in 1..N : tower[t] < 2 ^ D

====