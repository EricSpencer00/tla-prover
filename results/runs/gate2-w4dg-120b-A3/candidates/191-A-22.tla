---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, 8, ... for the D disks.
\* A tower's value is the sum of the sizes of the disks currently on it,
\* so its binary representation encodes which disks are present.
\* The total number of disks is conserved: the sum of all tower values is
\* always 2^D - 1 (all bits below D set).
Disks == { 1 << k : k \in 0 .. (D - 1) }

TopMask(t) == IF t = 0 THEN 0 ELSE ((1 << t) - 1)

VARIABLES towers

vars == << towers >>

TypeOK ==
  /\ towers \in [0 .. (N - 1) -> 0 .. ((1 << D) - 1)]
  /\ D \in Nat /\ N \in Nat

Init ==
  /\ towers = [i \in 0 .. (N - 1) |-> IF i = 0 THEN ((1 << D) - 1) ELSE 0]

\* A move may only pick the smallest disk present on the source tower,
\* so the bits below it must be zero. It may only drop onto a tower that
\* has no smaller disk already present (its lower bits are zero).
Move ==
  \E d \in Disks :
    /\ (TopMask(D) & d) = d
    /\ \E src \in 0 .. (N - 1), dst \in 0 .. (N - 1) :
         /\ src # dst
         /\ (towers[src] & d) = d
         /\ (towers[src] & (d - 1)) = 0
         /\ (towers[dst] & (d - 1)) = 0
         /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == Move

Spec == Init /\ [][Next]_vars

Inv == \A i \in 0 .. (N - 1) : towers[i] <= ((1 << D) - 1)

====