---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are binary-encoded sums of disk values; a disk of size k is the
\* power of two 2^k. DiskCount is the number of bits/disk positions.
DiskCount == D
DiskValue(k) == 1 << k
AllDisks == (1 << DiskCount) - 1
Towers == 0 .. (N - 1)

VARIABLES value

vars == <<value>>

TypeOK == /\ value \in [Towers -> 0 .. AllDisks]
          /\ DiskCount \in Nat
          /\ N \in Nat
          /\ DiskCount >= 1
          /\ N >= 1

Init == /\ value = [t \in Towers |-> IF t = 0 THEN AllDisks ELSE 0]
        /\ DiskCount = D
        /\ N = N

\* The smallest disk on a tower is its least significant set bit; that disk is
\* exactly the tower's value when it is a power of two.
SmallestDisk(t) == value[t]

LegalMove(d, src, dst) ==
  /\ src # dst
  /\ d >= 1
  /\ d <= AllDisks
  /\ (d & (d - 1)) = 0
  /\ (value[src] # 0 /\ (value[src] & d) # 0)
  /\ (value[src] >= d /\ (value[src] - d) # 0 => (value[src] & (d - 1)) = 0)
  /\ (value[dst] >= d => (value[dst] & (d - 1)) = 0)

Move(d, src, dst) ==
  /\ LegalMove(d, src, dst)
  /\ value' = [value EXCEPT ![src] = @ - d, ![dst] = @ + d]
  /\ UNCHANGED <<DiskCount, N>>

Next == \E d \in 1 .. AllDisks, src \in Towers, dst \in Towers : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the tower values always sum to the full set of disks.
Inv == value[0] + value[1] + value[2] = AllDisks

====