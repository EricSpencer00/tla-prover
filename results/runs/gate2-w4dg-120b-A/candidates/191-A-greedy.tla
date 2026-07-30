---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode the set of disks on that tower as a bitmask: bit k
\* (value 2^k) is set iff the disk of size 2^k is present. The sum of all
\* tower values is therefore the sum of all disk values, which is 2^D-1.
\* Conservation of that sum is the safety property that no disk is ever
\* created or destroyed.

VARIABLES towers

vars == <<towers>>

\* Bitwise AND in pure TLA+: a & b is the sum of the powers of two that are
\* present in both a and b. This is the arithmetic definition of the
\* bitwise AND operator, used to test disk presence and ordering.
BitwiseAnd(a, b) ==
  LET bits == {k \in 0..(D - 1) : (2^k) \in {x \in {1, 2, 4, 8, 16, 32, 64} : x <= a /\ x <= b}}
  IN  IF bits = {} THEN 0 ELSE LET k == CHOOSE x \in bits : TRUE IN 2^k + BitwiseAnd(a - 2^k, b)

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move is legal only if the disk is present on the source tower, is the
\* smallest disk on that tower, and cannot be placed on a smaller disk.
Move(d, src, dst) ==
  /\ src # dst
  /\ d \in {2^k : k \in 0..(D - 1)}
  /\ BitwiseAnd(towers[src], d) = d
  /\ BitwiseAnd(towers[src], d - 1) = 0
  /\ BitwiseAnd(towers[dst], d - 1) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in {2^k : k \in 0..(D - 1)} : \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ towers \in [1..N -> 0..(2^D - 1)]

Inv ==
  /\ LET Sum == [i \in 1..N |-> IF i = 1 THEN towers[i] ELSE towers[i - 1] + towers[i]]
     IN Sum[N] = 2^D - 1

====