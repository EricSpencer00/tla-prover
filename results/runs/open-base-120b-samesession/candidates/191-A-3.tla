---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

VARIABLES towers

(*--- Disk set ---*)
Disk == { 2 ^ k : k \in 0..D-1 }

AllDisks == 2 ^ D - 1

(*--- Initial state ---*)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*--- Helper predicates ---*)
IsOn(v, d) == (v \div d) % 2 = 1

IsSmallest(v, d) ==
    /\ IsOn(v, d)
    /\ \A e \in Disk: e < d => ~IsOn(v, e)

CanMove(src, dst, d) ==
    /\ src # dst
    /\ src \in 1..N
    /\ dst \in 1..N
    /\ d \in Disk
    /\ IsSmallest(towers[src], d)
    /\ \A e \in Disk: e < d => ~IsOn(towers[dst], e)

(*--- Next-state relation ---*)
Next ==
    \E src \in 1..N :
        \E dst \in 1..N :
            \E d \in Disk :
                /\ CanMove(src, dst, d)
                /\ towers' = [i \in 1..N |
                        IF i = src THEN towers[i] - d
                        ELSE IF i = dst THEN towers[i] + d
                        ELSE towers[i]]

(*--- Specification ---*)
Spec == Init /\ [] [Next]_towers

(*--- Invariants ---*)
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2 ^ D

Inv == (\Sum i \in 1..N: towers[i]) = AllDisks

====