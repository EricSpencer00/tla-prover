---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two, and a tower's value is the sum of the disks on it,
\* so its binary representation encodes the set of disks present and their ordering.
\* Moving a disk moves exactly that power of two from one tower value to another.

DiskValues == { 2 ^ k : k \in 0..(D - 1) }

VARIABLES towers

vars == <<towers>>

\* The sum of tower values always equals the sum of all disk values, which is
\* 2^D - 1: conservation of the total disk "mass".
RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ {x})

Total == 2 ^ D - 1

TypeOK ==
  /\ towers \in [0..(N - 1) -> 0..Total]
  /\ Total == 2 ^ D - 1

Init ==
  /\ towers = [i \in 0..(N - 1) |-> IF i = 0 THEN Total ELSE 0]

\* A disk can be moved only if it is present on the source and is the smallest
\* on that tower (all lower-order bits are clear); the destination must be empty
\* or hold only larger disks (its lower bits are clear).
Move(d, s, t) ==
  /\ d \in DiskValues
  /\ s # t
  /\ (towers[s] % (2 * d) >= d)
  /\ (towers[t] % (2 * d) = 0)
  /\ towers[s] >= d
  /\ towers' = [towers EXCEPT ![s] = @ - d, ![t] = @ + d]
  /\ UNCHANGED << >>

Next ==
  \/ \E d \in DiskValues, s \in 0..(N - 1), t \in 0..(N - 1) : Move(d, s, t)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ SumOf({towers[i] : i \in 0..(N - 1)}) = Total
  /\ \A i \in 0..(N - 1) : towers[i] <= Total

====