---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of distinct powers of two; each bit position represents
\* one disk (size 2^k). Conservation is a sum over all towers, not per tower.
VARIABLES towers

vars == <<towers>>

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move is legal if the disk is present, is the smallest on its tower, and the
\* destination tower has no smaller disk already present.
Move(d, src, dst) ==
  /\ src # dst
  /\ towers[src] >= d
  /\ towers[dst] >= d
  /\ (towers[src] \div d) % 2 = 1
  /\ (towers[src] \div (2 * d)) % 2 = 0
  /\ \/ (towers[dst] = 0)
     \/ ((towers[dst] \div d) % 2 = 1 /\ (towers[dst] \div (2 * d)) % 2 = 0)
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in 1..(2^D - 1) : \E src \in 1..N : \E dst \in 1..N : Move(d, src, dst)

\* Conservation of the bitwise-encoded disk set across all towers.
Inv == (towers[1] + towers[2] + (IF N >= 3 THEN towers[3] ELSE 0)
           + (IF N >= 4 THEN towers[4] ELSE 0)
           + (IF N >= 5 THEN towers[5] ELSE 0)
           + (IF N >= 6 THEN towers[6] ELSE 0)
           + (IF N >= 7 THEN towers[7] ELSE 0)
           + (IF N >= 8 THEN towers[8] ELSE 0)) = 2^D - 1

Spec == Init /\ [][Next]_vars

====