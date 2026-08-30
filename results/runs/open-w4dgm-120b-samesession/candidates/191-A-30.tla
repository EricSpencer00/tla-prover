---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are interpreted as bitsets: a power-of-two disk is on a tower
\* exactly when its bit is set in that tower's value. Conservation holds on the
\* sum of tower values, which is the sum over powers of two.
VARIABLES towers

vars == <<towers>>

RECURSIVE SumOf(_)
SumOf(n) == IF n = 0 THEN 0 ELSE towers[n] + SumOf(n - 1)

\* A power of two is present in a tower value exactly when the value AND the disk
\* equals the disk; the shift-and-mask below computes the disk's lowest set bit.
Disk(v) == IF v = 0 THEN 0 ELSE 2 ^ (v - 1)

\* Smallest disk on a tower: v must be a power of two, so its lowest set bit is
\* itself and the test v = Disk(v) holds exactly for the smallest disk.
SmallestDisk(v) == IF v = Disk(v) THEN v ELSE 0

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]
    /\ UNCHANGED << >>

\* A move is legal only if the disk is the smallest on its source and no smaller
\* disk is already present on the destination.
Move(disk, from, to) ==
    /\ from # to
    /\ (towers[from] AND disk) = disk
    /\ (towers[from] AND (disk - 1)) = 0
    /\ (towers[to] AND (disk - 1)) = 0
    /\ towers' = [towers EXCEPT ![from] = towers[from] - disk, ![to] = towers[to] + disk]
    /\ UNCHANGED << >>

Next ==
    \E disk \in {2 ^ k : k \in 0..(D - 1)}, from \in 1..N, to \in 1..N : Move(disk, from, to)

Spec == Init /\ [][Next]_vars

TypeOK == \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

\* The total number of disks never changes, since every move only relocates one.
Conservation == SumOf(N) = (2 ^ D) - 1

\* The whole puzzle solves when EVERY disk sits on the last tower.
Inv == towers[N] = (2 ^ D) - 1
====