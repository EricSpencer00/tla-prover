---- MODULE Hanoi ----
EXTENDS Naturals, Integers

CONSTANTS D, N

\* Tower values are bitwise sums of disk-values (powers of two). Disk k has
\* value 2^k and appears on a tower iff the corresponding bit is set.
Disks == 1 << D - 1
TowerValues == {0, 1, 3, 7, 15, 31, 63}
TowerIndices == 0 .. (N - 1)
DiskValues == {1 << k : k \in 0 .. (D - 1)}
LargestDisk == 1 << (D - 1)

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

VARIABLES towers

vars == <<towers>>

TypeOK ==
  /\ towers \in [TowerIndices -> TowerValues]
  /\ SumOf(towers, TowerIndices) = Disks

Init ==
  /\ towers = [i \in TowerIndices |-> IF i = 0 THEN Disks ELSE 0]

Clear(v, d) == v /\ ~(d)

Move(d, src, dst) ==
  /\ src # dst
  /\ towers[src] >= d
  /\ Clear(towers[src], d) = towers[src] - d
  /\ towers[dst] * d = 0
  /\ towers' = [towers EXCEPT ![src] = towers[src] - d, ![dst] = towers[dst] + d]

Next ==
  \/ \E d \in DiskValues, src \in TowerIndices, dst \in TowerIndices : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* No liveness below: the goal is a negated invariant, not an actual property.
Inv == TypeOK

====