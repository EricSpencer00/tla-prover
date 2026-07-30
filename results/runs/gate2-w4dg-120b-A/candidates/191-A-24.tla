---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi model. Each tower's value is the sum of the powers of two
\* representing the disks currently on it; the bits set in the value are the
\* disks present. Disks are moved one at a time, and a move of a disk d is
\* only legal if d is the smallest disk on its source tower and the destination
\* tower holds no smaller disk.

CONSTANTS D, N

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES towers

vars == <<towers>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

Total == SumOf([i \in 1 .. N |-> towers[i]], 1 .. N)

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* Disk d may move from tower i to tower j only if it is the smallest disk on
\* tower i AND tower j has no smaller disk of its own.
Move(d, i, j) ==
  /\ i # j
  /\ towers[i] >= d
  /\ towers[j] + d < 2 ^ D
  /\ (towers[i] % (2 * d)) = d
  /\ (towers[j] % (2 * d)) = 0
  /\ towers' = [towers EXCEPT ![i] = @ - d, ![j] = @ + d]

Next ==
  \/ \E d \in Disks : \E i \in 1 .. N, j \in 1 .. N : Move(d, i, j)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ Total = (2 ^ D) - 1
  /\ TypeOK

====