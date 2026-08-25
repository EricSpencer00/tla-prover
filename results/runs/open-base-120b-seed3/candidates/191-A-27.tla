---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANT D, N

VARIABLES towers

(*--- Disk definitions ---------------------------------------------------*)
Disk(i) == 2^i
DiskSet == { Disk(i) : i \in 0..(D-1) }

(*--- Helper predicates ---------------------------------------------------*)
DiskOn(t, d) == (t % (2 * d)) >= d          \* disk d is present on tower t
NoSmaller(t, d) == (t % d) = 0              \* no disk smaller than d on tower t

(*--- Initial state -------------------------------------------------------*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--- Next-state relation ------------------------------------------------*)
Next ==
    \/ \E src \in 1..N, dst \in 1..N, d \in DiskSet :
        /\ src # dst
        /\ DiskOn(towers[src], d)            \* d is on the source tower
        /\ NoSmaller(towers[src], d)         \* d is the smallest on source
        /\ NoSmaller(towers[dst], d)         \* destination has no smaller disk
        /\ towers' = [towers EXCEPT
                         ![src] = towers[src] - d,
                         ![dst] = towers[dst] + d]

(*--- Type correctness invariant ------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

(*--- Conservation invariant ---------------------------------------------*)
Inv ==
    /\ TypeOK
    /\ \Sum i \in 1..N: towers[i] = 2^D - 1

(*--- Specification -------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

====