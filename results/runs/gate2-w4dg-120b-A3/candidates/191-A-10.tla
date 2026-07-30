---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ... , 2^(D-1).  The
\* towers are numbered 1..N, and each tower's value is the sum of the
\* sizes of the disks it holds, encoded as a bitset.
Towers == 1..N

\* Disk(k) is the size of the k-th smallest disk, and the smallest
\* disk is Disk(1).  The maximum bit position is D, so the total
\* number of disks is fixed and always conserved.
Disk(k) == 2^(k - 1)

\* BitSet(d) is the bitmask for a single disk; the whole puzzle starts
\* as a single contiguous bitset on the first tower.
BitSet(d) == 2^(d - 1)

Total == 2^D - 1

VARIABLES tower

vars == <<tower>>

Sum == tower[1] + tower[2] + tower[3]

Init ==
  /\ tower = [t \in Towers |-> IF t = 1 THEN Total ELSE 0]

\* A move may only take the smallest disk on a tower (no smaller disk
\* underneath it) and may only land on a tower with no smaller disk.
Move(d, from, to) ==
  /\ from # to
  /\ from \in Towers
  /\ to \in Towers
  /\ tower[from] >= BitSet(d)
  /\ (tower[from] % (2 * BitSet(d))) >= BitSet(d)
  /\ ((tower[to] % (2 * BitSet(d))) = 0 \/ tower[to] = 0)
  /\ tower' = [tower EXCEPT ![from] = tower[from] - BitSet(d), ![to] = tower[to] + BitSet(d)]

Next ==
  \/ \E d \in 1..D, from \in Towers, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ tower \in [Towers -> 0..Total]
  /\ tower[1] >= tower[2]
  /\ tower[2] >= tower[3]

Inv ==
  /\ Sum = Total
  /\ \A t \in Towers : tower[t] < 2^D

====