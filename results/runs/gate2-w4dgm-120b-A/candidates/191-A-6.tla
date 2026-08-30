---- MODULE Hanoi ----
\* Bitwise Tower of Hanoi: each tower's value is the sum of the powers-of-two
\* disk sizes sitting on it, so the bits set in that value name the disks.
\* A legal move removes a disk that is the smallest present on its tower
\* and lands it on a target tower whose smallest present is no smaller.
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are the first D powers of two; their sum is the full stack mask.
\* Tower[t] holds the summed size of every disk currently on tower t.
VARIABLES tower

vars == <<tower>>

FullMask == 2^D - 1

TypeOK ==
  /\ tower \in [0..(N - 1) -> 0..FullMask]

Init ==
  /\ tower = [i \in 0..(N - 1) |-> IF i = 0 THEN FullMask ELSE 0]

\* Bitwise AND: test whether mask bits are set in a tower value.
MaskOf(k) == 2^k
BitsSet(v) == { k \in 0..(D - 1) : (v \div 2^k) % 2 = 1 }

Move(d, src, dst) ==
  /\ d \in 1..FullMask
  /\ d * 2 <= 2^D
  /\ src # dst
  /\ (tower[src] \div d) % 2 = 1
  /\ \A k \in BitsSet(tower[src]) : k >= BitsSet(d)[1]
  /\ \A k \in BitsSet(tower[dst]) : k >= BitsSet(d)[1]
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in 1..FullMask, src, dst \in 0..(N - 1) : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: no disk is created or destroyed, so towers always sum to the
\* full stack mask, and tower values stay within their bounded range.
Conservation == tower[0] + tower[1] + tower[2] = FullMask
\* The full mask bound is already covered by the individual towers' range,
\* but TLC expects a named invariant for each listed property.
BoundedTower == \A i \in 0..(N - 1) : tower[i] <= FullMask

====