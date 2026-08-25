---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

\* Set of disk values (each a distinct power of two)
Disk == { 2^k : k \in 0..D-1 }

\* Test whether disk d (a power of two) is present in tower value t
IsOn(t, d) == (t % (2 * d)) >= d

\* Test that all disks smaller than d are absent from tower value t
LowerBitsZero(t, d) == (t % d) = 0

\* Initial state: all disks on tower 1, others empty
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* One legal move of disk d from src to dst
Next ==
    \/ \E d \in Disk:
        \E src \in 1..N:
            \E dst \in 1..N:
                /\ src # dst
                /\ IsOn(towers[src], d)
                /\ LowerBitsZero(towers[src], d)      \* d is the smallest on src
                /\ LowerBitsZero(towers[dst], d)      \* no smaller disk on dst
                /\ towers' = [towers EXCEPT
                                 ![src] = towers[src] - d,
                                 ![dst] = towers[dst] + d]

\* Full specification (no liveness)
Spec == Init /\ [][Next]_towers

\* Type correctness invariant
TypeOK == /\ towers \in [1..N -> Nat]
          /\ \A i \in 1..N: towers[i] >= 0 /\ towers[i] < 2^D

\* Conservation invariant (all disks accounted for)
Inv == +/ i \in 1..N: towers[i] = 2^D - 1
====