---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

VARIABLES towers

\* The set of disks, each represented by a distinct power of two
Disks == { 2 ^ i : i \in 0..D-1 }

\* Test whether disk d (a power of two) is present in tower value v
IsOn(v, d) == (v % (2 * d)) >= d

\* d is the smallest disk on tower v
IsSmallest(v, d) ==
    IsOn(v, d) /\ \A d2 \in Disks : (d2 < d) => ~IsOn(v, d2)

\* Destination tower v can accept disk d (no smaller disk present)
DestOK(v, d) ==
    (v = 0) \/ \A d2 \in Disks : (d2 < d) => ~IsOn(v, d2)

\* Initial state: all disks on the first tower
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

\* One legal move of a smallest disk from a source tower to a destination tower
Move ==
    \E d \in Disks :
        \E s \in 1..N :
            \E t \in 1..N :
                /\ s # t
                /\ IsOn(towers[s], d)
                /\ IsSmallest(towers[s], d)
                /\ DestOK(towers[t], d)
                /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                            ![t] = towers[t] + d]

Next == Move

\* Specification
Spec == Init /\ [][Next]_towers

\* Type correctness: each tower value is a natural number less than 2^D
TypeOK == \A i \in 1..N : towers[i] \in Nat /\ towers[i] < 2 ^ D

\* Conservation invariant: sum of all tower values equals total disk weight
Inv == (\Sum i \in 1..N : towers[i]) = 2 ^ D - 1

====