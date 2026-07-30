---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Each tower's value is a sum of powers of two, one per disk present on it.
\* Disk k has size 2^k (k=0..D-1), so the set of present disks is exactly the bits
\* set in the tower's binary representation.
\* Conservation is expressed as the sum of tower values, not as a token count.
\* Bitwise AND is defined as an arithmetic operator here (p & q = sum of powers
\* of two that appear in both p and q); a Java override may replace it.

PowerOfTwo(k) == 2 ^ k

TowerValues == [1..N -> 0..(PowerOfTwo(D) - 1)]

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

Total == SumOver(TowerValues, 1..N)

\* Bitwise AND: single-bit overlap between p and q, computed arithmetically.
BitAnd(p, q) ==
  LET bits == {k \in 0..(D - 1) : (p \div PowerOfTwo(k)) % 2 = 1 /\ (q \div PowerOfTwo(k)) % 2 = 1}
  IN Sum({PowerOfTwo(k) : k \in bits})

TypeOK ==
  /\ D \in Nat /\ D >= 1
  /\ N \in Nat /\ N >= 2
  /\ TowerValues \in [1..N -> 0..(PowerOfTwo(D) - 1)]

\* The only step in the system, taken nondeterministically over every legal move.
Move(d, src, dst) ==
  /\ d \in {PowerOfTwo(k) : k \in 0..(D - 1)}
  /\ src # dst
  /\ (TowerValues[src] \div d) % 2 = 1
  /\ BitAnd(TowerValues[src], d - 1) = 0
  /\ BitAnd(TowerValues[dst], d - 1) = 0
  /\ TowerValues' = [TowerValues EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in {PowerOfTwo(k) : k \in 0..(D - 1)}:
    \E src \in 1..N: \E dst \in 1..N:
      Move(d, src, dst)

\* All disks start on the first tower; nothing else is ever placed there.
Init ==
  /\ TowerValues[1] = PowerOfTwo(D) - 1
  /\ \A t \in 1..N \ {1} : TowerValues[t] = 0

\* Conservation: the total sum of tower values never changes.
Inv == Total = PowerOfTwo(D) - 1

Spec == Init /\ [][Next]_TowerValues

====