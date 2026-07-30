---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ... 2^(D-1).
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

\* Tower[t] is the sum of the disk-values on tower t; its bits encode presence.
VARIABLES Tower

vars == <<Tower>>

RECURSIVE SumOf(_, _)
SumOf(S, f) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(S \ {x}, f)

\* The total bits set across all towers is the all-ones mask for D disks.
AllDisks == 2 ^ D - 1

\* A disk is the smallest on a tower if no smaller bit is set on that tower.
SmallestOn(t, d) == \A k \in 0 .. (D - 1) : (2 ^ k < d) => ((Tower[t] % (2 ^ (k + 1))) < 2 ^ k)

Init ==
    /\ Tower = [t \in 0 .. (N - 1) |-> IF t = 0 THEN AllDisks ELSE 0]

\* One disk moves from a source tower to a destination tower.
Move(d, src, dst) ==
    /\ src # dst
    /\ d \in Disks
    /\ (Tower[src] % (2 * d)) >= d
    /\ SmallestOn(src, d)
    /\ SmallestOn(dst, d)
    /\ Tower' = [Tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \/ \E d \in Disks, src \in 0 .. (N - 1), dst \in 0 .. (N - 1) : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ Tower \in [0 .. (N - 1) -> 0 .. (2 ^ D - 1)]
    /\ SumOf(0 .. (N - 1), Tower) = AllDisks

Inv == SumOf(0 .. (N - 1), Tower) = AllDisks

====