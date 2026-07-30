---- MODULE Hanoi ----
EXTENDS Naturals

\* The Tower of Hanoi puzzle. Disk positions are encoded bitwise in per-tower
\* values: tower t holds the sum of its disks' power-of-two sizes, so a set of
\* disks is a contiguous block of low-order bits. The invariant protects the
\* bitwise encoding (each tower value stays under 2^D and the total is conserved).
\* A move moves one disk, which must be the smallest on its source tower, onto
\* a destination tower that is empty or has no smaller disk already on it.

CONSTANTS D, N

Disks == { 2 ^ k : k \in 0..(D - 1) }
Towers == 1..N
AllDisks == 2 ^ D - 1

RECURSIVE Pop(_)
Pop(n) ==
  IF n = 0 THEN 0
  ELSE LET lo == n % 2 IN IF lo = 0 THEN Pop(n \div 2) ELSE lo

RECURSIVE SumS(_)
SumS(m) ==
  IF m = 0 THEN 0
  ELSE SumS(m - 1) + DiskOn[m]

VARIABLES tower

vars == <<tower>>

TypeOK ==
  /\ tower \in [Towers -> 0..AllDisks]
  /\ \A t \in Towers : tower[t] <= AllDisks

Init ==
  /\ tower = [t \in Towers |-> IF t = 1 THEN AllDisks ELSE 0]

\* The smallest disk on a tower is its lowest set bit (Pop returns exactly that).
Smallest(t) == Pop(tower[t])

PossibleMove(d, src, dst) ==
  /\ src # dst
  /\ (tower[src] % (2 * d) = d)
  /\ (tower[dst] % (2 * d) = 0)

Move(d, src, dst) ==
  /\ PossibleMove(d, src, dst)
  /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in Disks, s \in Towers, t \in Towers : Move(d, s, t)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E d \in Disks, s \in Towers, t \in Towers : Move(d, s, t))

\* Conservation of mass: tower values are an exact partition of AllDisks.
Inv ==
  /\ TypeOK
  /\ SumS(N) = AllDisks

====