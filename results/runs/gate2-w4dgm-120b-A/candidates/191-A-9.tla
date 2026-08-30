---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Disk of size 2^k is the k-th smallest; tower value is the sum of present disks
\* (bits set exactly for the disks on that tower). Conservation of the sum of
\* tower values is the disk-conservation fact this puzzle relies on.
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET d == CHOOSE e \in S : TRUE IN d + SumOf(S \ { d })

VARIABLES towers

TypeOK == towers \in [1 .. N -> 0 .. (2 ^ D) - 1]

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* A move is physically valid only if the disk is present on the source tower
\* and is the smallest disk there, and the destination has no smaller disk.
Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ towers[src] >= d
  /\ (towers[src] % (2 * d)) = d
  /\ towers[dst] % (2 * d) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in Disks : \E src \in 1 .. N : \E dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_towers

\* Conservation: the total number of disks present across all towers never
\* changes -- none is created or destroyed by a move.
Inv == SumOf({ towers[i] : i \in 1 .. N }) = (2 ^ D) - 1

====