---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

RECURSIVE SumOf(_, _)
SumOf(seq, lo) ==
    IF lo = 0 THEN 0
    ELSE seq[lo] + SumOf(seq, lo - 1)

VARIABLES towers

vars == <<towers>>

\* An individual disk is a power of two; bit k (value 2^k) is the disk of size 2^k.
\* Tower t's value is the sum of the disks currently on it, so its binary bits are
\* exactly the occupancy set. Conservation is the sum of all tower values.
Disk(k) == 2 ^ k

RECURSIVE Bits3(_, _)
Bits3(n, k) ==
    IF k = 0 THEN n
    ELSE IF k = 1 THEN 0
    ELSE Bits3(n \div 2, k - 1)

\* A tower's low bits cleared: Bits3(towers[t], k) is the value of tower t with
\* all bits below k zeroed out, used to test if a smaller disk is present.
Cleared(t, k) == Bits3(towers[t], k)

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]

Init ==
    /\ towers \in {t \in [1..N -> 0..(2 ^ D - 1)] : t[1] = 2 ^ D - 1}
    /\ UNCHANGED <<>>

\* A move is legal only if the moving disk is the smallest on its source tower
\* and not placed onto a smaller disk on the destination tower.
Move(disk, src, dst) ==
    /\ src # dst
    /\ towers[src] >= disk
    /\ (towers[src] \div disk) % 2 = 1
    /\ (towers[dst] = 0 \/ (towers[dst] \div disk) % 2 = 0)
    /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]
    /\ UNCHANGED <<>>

Next ==
    \/ \E disk \in {Disk(k) : k \in 0..(D - 1)} : \E src, dst \in 1..N : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: all tower values sum to the full set of disks (nothing lost).
Inv ==
    SumOf(towers, N) = (2 ^ D - 1)

====