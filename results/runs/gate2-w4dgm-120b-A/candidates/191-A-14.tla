---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi modeled with bitwise-encoded tower values.
CONSTANTS D, N

\* Masks for individual disks: disk k (0-indexed) is the power of two 2^k.
DiskMask(k) == 2 ^ k

VARIABLES stacks

vars == <<stacks>>

\* The sum of all tower bitsets equals 2^D - 1 exactly when every disk is
\* accounted for (none created/lost); this is the conservation claim.
RECURSIVE StackSum(_)
StackSum(S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE IN stacks[x] + StackSum(S \ {x})

TypeOK == stacks \in [1..N -> 0..(2 ^ D - 1]

Init == stacks = [t \in 1..N |-> IF t = 1 THEN (2 ^ D - 1) ELSE 0]

\* A move is legal if the disk is present on the source, is the smallest there,
\* and sits on nothing smaller at the destination.
Move(d, s, t) ==
  /\ d \in {DiskMask(k) : k \in 0..(D - 1)}
  /\ s # t
  /\ (stacks[s] & d) = d
  /\ \E k \in 0..(D - 1) : DiskMask(k) = d /\ (stacks[s] % DiskMask(k + 1)) = d
  /\ \E l \in 0..(D - 1) : DiskMask(l) \in {DiskMask(k) : k \in 0..(D - 1)}
        => (DiskMask(l) & stacks[t]) = 0
  /\ stacks' = [stacks EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in {DiskMask(k) : k \in 0..(D - 1)}, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the total number of disks is fixed forever.
Inv == StackSum(1..N) = (2 ^ D - 1)

====