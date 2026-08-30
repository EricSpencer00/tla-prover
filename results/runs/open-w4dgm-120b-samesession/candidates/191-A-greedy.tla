---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower values are sums of disk values (powers of two); a set bit means that
\* disk is present on the tower. Conservation is the sum of all tower values.
VARIABLES towers

vars == <<towers>>

TypeOK == /\ towers \in [1..N -> 0..(2^D - 1)]
          /\ \A i \in 1..N : towers[i] >= 0

Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* A move is legal only if the disk is the smallest on its source tower and
\* the destination tower has no smaller disk already on it.
Move(d, src, dst) ==
  /\ d \in {2^k : k \in 0..(D - 1)}
  /\ src # dst
  /\ towers[src] >= d
  /\ (towers[src] % (2 * d)) = d
  /\ (towers[dst] % (2 * d)) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in {2^k : k \in 0..(D - 1)} \E src \in 1..N \E dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the total disk value is invariant -- no move creates or loses a disk.
Inv == (towers[1] + towers[2] + towers[3]) = (2^D - 1)

====