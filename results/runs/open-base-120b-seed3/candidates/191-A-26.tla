---- MODULE Hanoi ----
EXTENDS Naturals, Sequences

CONSTANTS D, N

VARIABLES tower

(*--- Helper definitions ---*)
Disk(d) == 2 ^ (d - 1)

IsPresent(t, disk) == (t % (2 * disk) >= disk)

IsSmallest(t, disk) == IsPresent(t, disk) /\ (t % disk = 0)

DestOk(t, disk) == (t % disk = 0)

Sum(t) == \SUM i \in 1..N: t[i]

(*--- Initialization ---*)
Init ==
    tower = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

(*--- Move action ---*)
Move ==
    \E d \in 1..D:
        \E src \in 1..N:
            \E dst \in 1..N:
                /\ src # dst
                /\ IsPresent(tower[src], Disk(d))
                /\ IsSmallest(tower[src], Disk(d))
                /\ DestOk(tower[dst], Disk(d))
                /\ tower' = [tower EXCEPT ![src] = tower[src] - Disk(d),
                                         ![dst] = tower[dst] + Disk(d)]

Next == Move

(*--- Specification ---*)
Spec == Init /\ [][Next]_tower

(*--- Invariants ---*)
TypeOK == /\ tower \in [1..N -> Nat]
          /\ \A i \in 1..N: tower[i] < 2 ^ D

Inv == /\ TypeOK
       /\ Sum(tower) = (2 ^ D) - 1

====