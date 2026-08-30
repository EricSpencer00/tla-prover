---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1 /\ N \in Nat /\ N >= 2

VARIABLES towers

vars == <<towers>>

\* Disk k has value 2^k (size grows with k); a tower's value is the sum of
\* the disk values it holds, so its binary bits encode exactly which disks
\* are present on that tower.
Disk(k) == 2 ^ k
Total == 2 ^ D - 1

OnTower(k, i) == (towers[i] \div Disk(k)) % 2 = 1

InitMask(i) == IF i = 1 THEN Total ELSE 0

TypeOK ==
    /\ towers \in [1..N -> 0..Total]

Init ==
    /\ towers = [i \in 1..N |-> InitMask(i)]

\* A move relocates one disk from a source tower to a destination tower,
\* always the smallest disk on the source and never onto a smaller disk.
Move(d, from, to) ==
    /\ d \in {Disk(k) : k \in 0..(D - 1)}
    /\ from # to
    /\ OnTower(LN(d), from)
    /\ \A k \in 0..(D - 1) : (Disk(k) < d) => ~OnTower(k, from)
    /\ \A k \in 0..(D - 1) : (Disk(k) < d) => ~OnTower(k, to)
    /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
    \E d \in {Disk(k) : k \in 0..(D - 1)} : \E from \in 1..N : \E to \in 1..N : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise encoding is a plain integer sum, so every move
\* must preserve the grand total of all disk values.
Conservation ==
    towers[1] + towers[2] + (IF N >= 3 THEN towers[3] ELSE 0)
        + (IF N >= 4 THEN towers[4] ELSE 0)
        + (IF N >= 5 THEN towers[5] ELSE 0) = Total

TowerMask(i) == towers[i]

Inv ==
    /\ Conservation
    /\ TowerMask(1) \in Nat
    /\ TowerMask(N) \in Nat
    /\ \A i \in 1..N : TowerMask(i) <= Total

====