---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ N \in Nat /\ D >= 2 /\ N >= 2

\* The tower states are stored as natural numbers whose binary representation
\* encodes which disks (powers of two) are present on each tower.
\* Conservation is the bitwise-sum-of-disk-values accounting identity.
VARIABLES towers

vars == <<towers>>

TypeOK == /\ towers \in [1..N -> 0..(2^D) - 1]
          /\ \A t \in 1..N : towers[t] >= 0 /\ towers[t] < 2^D

Disk(k) == 2^k

\* The smallest disk on a tower is the lowest set bit; masking lower bits == 0
\* (no smaller disk underneath) is the only way to tell which disk may move.
SmallestDiskOn(t) ==
  CHOOSE k \in 0..(D - 1) : (towers[t] /\ Disk(k)) = Disk(k)

DiskPresent(d, t) == (towers[t] /\ d) = d

Init ==
  /\ towers = [t \in 1..N |-> IF t = 1 THEN (2^D) - 1 ELSE 0]

Move(d, src, dst) ==
  /\ src # dst
  /\ DiskPresent(d, src)
  /\ d = SmallestDiskOn(src)
  /\ \A k \in 0..(D - 1) : Disk(k) < d => DiskPresent(Disk(k), dst) = FALSE
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in { Disk(k) : k \in 0..(D - 1) } :
    \E src, dst \in 1..N :
      Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise-encoded tower values always sum to the full disk set.
Inv ==
  /\ \A t \in 1..N : towers[t] >= 0 /\ towers[t] < 2^D
  /\ (towers[1] + towers[2] + towers[3]) = (2^D) - 1

\* The puzzle's liveness is explored via the negated goal as an invariant.
GoalNotReached == towers[N] # (2^D) - 1

====