---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower[i] is the bitwise-encoded set of disks on tower i: disk k has size 2^k,
\* so the sum of tower values is the natural number whose bits are exactly the
\* disks present. Conservation of disk count is the invariant that this sum
\* stays equal to 2^D - 1 (the packed value of all disks together).
VARIABLES Tower

TypeOK ==
  /\ Tower \in [1..N -> 0..(2^D - 1)]

\* Sum of all tower values: each disk's value is accounted for once, so the
\* sum always equals the packed value of the full disk set.
RECURSIVE SumT(_)
SumT(S) ==
  IF S = {} THEN 0
  ELSE LET t == CHOOSE x \in S : TRUE IN Tower[t] + SumT(S \ {t})

\* Disk k is present on tower i iff bit k of Tower[i] is 1.
HasDisk(i, k) == (Tower[i] DIV 2^k) % 2 = 1

Init ==
  /\ Tower = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* Bitwise-AND in pure TLA+: the expression is nonzero exactly when the two
\* tower values share a set bit, i.e. have a disk in common.
CommonBits(i, j) == Tower[i] * Tower[j] = Tower[i] * Tower[i] + Tower[j] * Tower[j]

\* Lower bits below k are all zero on tower i: no disk smaller than 2^k sits
\* there, which is what makes 2^k the smallest disk on that tower.
LowerBitsZero(i, k) == Tower[i] % 2^k = 0

Move(d, i, j) ==
  /\ Tower[i] >= d
  /\ HasDisk(i, d)
  /\ LOWER(i, d)
  /\ LOWER(j, d)
  /\ i # j
  /\ Tower' = [Tower EXCEPT ![i] = Tower[i] - d, ![j] = Tower[j] + d]

\* LOWER(i, d) is the small-disk test for the single disk value d = 2^k; it
\* has to compute k = log2(d) on the fly, so it is defined as an operator.
LOWER(i, d) ==
  \E k \in 0..(D - 1) : d = 2^k /\ LowerBitsZero(i, k)

Next ==
  \E d \in {2^k : k \in 0..(D - 1)} : \E i, j \in 1..N : Move(d, i, j)

\* The spec never reaches a final state: the empty set of reachable states
\* satisfies every liveness formula, so a negated-goal invariant is the
\* only way to see the solution path (via a counterexample trace).
Spec == Init /\ [][Next]_Tower

Inv ==
  /\ SumT(1..N) = 2^D - 1
  /\ TypeOK

====