---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES tower

(*--- Disk set ----------------------------------------------------------------*)
DiskSet == { 2^i : i \in 0..D-1 }

(*--- Helper predicates -------------------------------------------------------*)
DiskPresent(t, d) == (t % (2 * d) >= d)               \* bit d is set
SmallestOn(t, d) == DiskPresent(t, d) /\ (t % d = 0)  \* no smaller bits set
NoSmaller(t, d)   == (t % d = 0)                      \* destination has no smaller disk

(*--- Initialization ----------------------------------------------------------*)
Init ==
    /\ tower = [i \in 1..N |-> IF i = 1 THEN (2^D) - 1 ELSE 0]
    /\ TypeOK

(*--- Next-state relation -----------------------------------------------------*)
Next ==
    \E d \in DiskSet:
      \E s, t \in 1..N :
        /\ s # t
        /\ SmallestOn(tower[s], d)
        /\ NoSmaller(tower[t], d)
        /\ tower' = [i \in 1..N |-> 
                       IF i = s THEN tower[i] - d
                       ELSE IF i = t THEN tower[i] + d
                       ELSE tower[i]]
        /\ TypeOK

(*--- Type correctness invariant ---------------------------------------------*)
TypeOK ==
    /\ \A i \in 1..N : tower[i] \in Nat
    /\ \A i \in 1..N : tower[i] < 2^D

(*--- Safety invariant (conservation + type) ---------------------------------*)
Inv ==
    /\ TypeOK
    /\ (+/ i \in 1..N : tower[i]) = (2^D) - 1

(*--- Specification -----------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_tower

====