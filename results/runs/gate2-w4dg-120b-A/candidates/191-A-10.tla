---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values encode the set of disks on that tower as a bitmask: bit k
\* set iff the disk of size 2^k is present. The sum of all tower values
\* therefore equals the total weight of all disks, 2^D - 1.
Towers == 1..N
Disks == { 1 << k : k \in 0..(D - 1) }

VARIABLES towers

vars == <<towers>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOf(f, S \ {x})

\* Tower t is non-empty and its smallest-present disk is exactly x:
SmallestOn(t, x) ==
  /\ (towers[t] # 0)
  /\ ((towers[t] & (x - 1)) = 0)
  /\ ((towers[t] & x) = x)

\* Destination is empty or has no smaller disk than the one being moved:
DestinationClear(t, x) ==
  \/ (towers[t] = 0)
  \/ ((towers[t] & (x - 1)) = 0)

TypeOK == \A t \in Towers : towers[t] \in 0..(2^D - 1)

Init ==
  /\ towers = [t \in Towers |-> IF t = 1 THEN 2^D - 1 ELSE 0]

Move(x, src, dst) ==
  /\ src # dst
  /\ SmallestOn(src, x)
  /\ DestinationClear(dst, x)
  /\ towers' = [towers EXCEPT ![src] = @ - x, ![dst] = @ + x]

Next == \E x \in Disks, src, dst \in Towers : Move(x, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the sum of the bitmask values never changes -- no disk
\* is created or destroyed by any move.
Inv == SumOf(towers, Towers) = 2^D - 1

====