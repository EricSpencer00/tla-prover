---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--- Helper sets and predicates ---*)
DiskSet == { 2 ^ k : k \in 0..(D - 1) }

DiskOnSource(i, d) == ((towers[i] DIV d) % 2) = 1
SmallestOnSource(i, d) == towers[i] % d = 0
NoSmallerOnDest(j, d) == towers[j] % d = 0

(*--- Initialization ---*)
Init ==
    /\ towers[1] = 2 ^ D - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--- Move action ---*)
Move ==
    \E i, j \in 1..N :
        /\ i # j
        /\ \E d \in DiskSet :
            /\ DiskOnSource(i, d)
            /\ SmallestOnSource(i, d)
            /\ NoSmallerOnDest(j, d)
            /\ towers' = [towers EXCEPT ![i] = towers[i] - d,
                                         ![j] = towers[j] + d]

Next == Move

vars == <<towers>>

(*--- Specification ---*)
Spec == Init /\ [][Next]_vars

(*--- Invariants ---*)
TypeOK ==
    /\ \A i \in 1..N : towers[i] \in 0..(2 ^ D - 1)

Inv ==
    /\ Sum(i \in 1..N : towers[i]) = 2 ^ D - 1

====