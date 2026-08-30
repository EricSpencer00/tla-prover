---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode the set of disks present as a binary mask; the
\* conservation invariant then reads as a sum of masked values.
VARIABLES towers

vars == <<towers>>

\* Tower sum: each disk is powered of two, so the mask sum is linear.
RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumOf(S \ {x})

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN (2^D - 1) ELSE 0]
  /\ UNCHANGED <<>>

\* The smallest disk on a tower has all lower bits zero, so it lives at the
\* tower's current value's lowest set bit.
SmallestOn(i) == towers[i] - 2 * (towers[i] \div 2)

Move(d, from, to) ==
  /\ from # to
  /\ towers[from] >= d
  /\ d * 2 > towers[from]
  /\ towers[to] = 0 \/ d * 2 > towers[to]
  /\ towers' = [towers EXCEPT ![from] = towers[from] - d, ![to] = towers[to] + d]

Next ==
  \E d \in (1..(2^D - 1)) \ {0} : \E from \in 1..N, to \in 1..N : Move(d, from, to)

Spec == Init /\ [][Next]_vars

Conserved == SumOf(1..N) = 2^D - 1

GoalReached == towers[N] = 2^D - 1

Inv == TypeOK /\ Conserved

====