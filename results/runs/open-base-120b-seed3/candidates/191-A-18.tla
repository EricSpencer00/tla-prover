---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

(*--- Disk set: powers of two up to 2^(D-1) ---*)
DiskSet == { 2 ^ i : i \in 0..(D-1) }

(*--- Helper predicates ---*)
IsOn(t, d) == ((t \div d) % 2) = 1
IsSmallest(t, d) == IsOn(t, d) /\ (t % d = 0)

(*--- Initial state: all disks on tower 1 ---*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

(*--- One legal move ---*)
Move ==
    \E d \in DiskSet:
        \E s \in 1..N:
            \E dst \in 1..N:
                /\ s # dst
                /\ IsOn(towers[s], d)               \* disk present on source
                /\ (towers[s] % d = 0)               \* smallest on source
                /\ (towers[dst] % d = 0)             \* no smaller disk on dest
                /\ towers' = [towers EXCEPT ![s]   = towers[s] - d,
                                          ![dst] = towers[dst] + d]

Next == Move

(*--- Specification ---*)
Spec == Init /\ [][Next]_towers

(*--- Invariants ---*)
TypeOK == towers \in [1..N -> Nat] /\ \A i \in 1..N: towers[i] \in 0..(2 ^ D - 1)

Inv == \Sum i \in 1..N: towers[i] = (2 ^ D) - 1

====