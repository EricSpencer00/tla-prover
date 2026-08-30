---- MODULE Hanoi ----
\* Tower of Hanoi modeled with a bitwise per-tower encoding. Disk k has size
\* 2^k and is represented by the k-th bit; a tower's value is the sum of the
\* sizes of disks on it, so testing whether a disk is present or is the smallest
\* on its tower is a bitwise AND check against the tower value. Disks move one
\* at a time between towers, and must never be placed on a smaller disk.
EXTENDS Naturals

CONSTANTS D, N

\* Each tower holds a bitfield of disk sizes; the bit position equals the disk size's exponent.
Towers == 1..N
Disks == 1..D
DiskSize(k) == 2 ^ k
AllDisks == DiskSize(D) - 1

VARIABLES towers

vars == <<towers>>

OnTower(d, i) == towers[i] % (DiskSize(d) * 2) \div DiskSize(d) = 1
SmallestOn(t, d) == towers[t] % DiskSize(d + 1) = DiskSize(d)
NoSmallerOn(t, d) == towers[t] % DiskSize(d) = 0
SumTowers == towers[1] + towers[2] + towers[3]

TypeOK == towers \in [Towers -> 0..(DiskSize(D) - 1)]

Init == towers = [i \in Towers |-> IF i = 1 THEN AllDisks ELSE 0]

Move(d, from, to) ==
  /\ from # to
  /\ OnTower(d, from)
  /\ SmallestOn(from, d)
  /\ NoSmallerOn(to, d)
  /\ towers' = [towers EXCEPT ![from] = @ - DiskSize(d), ![to] = @ + DiskSize(d)]

Next == \E d \in Disks, from \in Towers, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* The puzzle conserves disks: towers always sum to the full set of disk sizes.
Inv == SumTowers = AllDisks

\* No liveness is claimed; model checking the negation of the solved state
\* produces a counterexample trace that is the solution.
====