---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--- Disk definitions ---*)
DiskSet == { 2 ^ i : i \in 0..D-1 }

AllDisks == 2 ^ D - 1

(*--- Initial state ---*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisks
    /\ \A i \in 1..N : (i # 1) => towers[i] = 0

(*--- Helper predicates ---*)
IsSmallestOn(t, d) ==
    /\ d \in DiskSet
    /\ towers[t] % (2 * d) = d

DestinationOK(dst, d) ==
    /\ towers[dst] % (2 * d) = 0 \/ towers[dst] % (2 * d) >= d

(*--- Move action ---*)
Move(d, src, dst) ==
    /\ src # dst
    /\ src \in 1..N /\ dst \in 1..N
    /\ d \in DiskSet
    /\ IsSmallestOn(src, d)
    /\ DestinationOK(dst, d)
    /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                               ![dst] = towers[dst] + d]

(*--- Next-state relation ---*)
Next ==
    \E d \in DiskSet :
        \E src \in 1..N :
            \E dst \in 1..N :
                Move(d, src, dst)

(*--- Invariants ---*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..AllDisks

Inv ==
    /\ \Sum i \in 1..N : towers[i] = AllDisks

(*--- Specification ---*)
Spec ==
    Init /\ [][Next]_towers

====