---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk k has size 2^k and is present on a tower iff bit k of that tower's
\* value is set. Tower values are summed, not bitvectors, so each tower is a
\* natural < 2^D and the whole puzzle conserves the sum of all disk sizes.
Disks == 1 << D - 1

RECURSIVE SumOf(_)
SumOf(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ {x})

VARIABLES towers
vars == <<towers>>

TypeOK == towers \in [1..N -> 0..(2^D - 1)]

Init ==
  /\ towers = [k \in 1..N |-> IF k = 1 THEN (2^D - 1) ELSE 0]
  /\ UNCHANGED towers

Move(d, src, dst) ==
  /\ d \in {1 << k : k \in 0..(D - 1)}
  /\ src # dst
  /\ (towers[src] # 0) /\ ((towers[src] \div d) * d = towers[src])
  /\ ((towers[src] \div (2 * d)) * (2 * d) = towers[src] \div 2)
  /\ IF towers[dst] = 0 THEN TRUE
     ELSE ((towers[dst] \div d) * d = towers[dst])
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in {1 << k : k \in 0..(D - 1)} \E src \in 1..N \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == SumOf(towers) = 2^D - 1
====