---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

VARIABLE towers

(*--- Derived constants and helper definitions ---*)
DiskVals == { 2 ^ (i - 1) : i \in 1..D }

AllDisks == 2 ^ D - 1

DiskPresent(val, d) == ((val \div d) % 2) = 1

IsSmallest(t, s, d) ==
    DiskPresent(t[s], d) /\ 
    \A d2 \in DiskVals : d2 < d => ~DiskPresent(t[s], d2)

NoSmaller(t, dst, d) ==
    \A d2 \in DiskVals : d2 < d => ~DiskPresent(t[dst], d2)

(*--- Initialization ---*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*--- Next-state relation ---*)
Next ==
    \E s \in 1..N :
        \E dst \in 1..N :
            /\ s # dst
            /\ \E d \in DiskVals :
                /\ IsSmallest(towers, s, d)
                /\ NoSmaller(towers, dst, d)
                /\ towers' = [i \in 1..N |
                                 IF i = s THEN towers[i] - d
                                 ELSE IF i = dst THEN towers[i] + d
                                 ELSE towers[i]]

(*--- Specification ---*)
Spec == Init /\ [][Next]_towers

(*--- Invariants ---*)
TypeOK ==
    \A i \in 1..N : towers[i] \in Nat /\ towers[i] < 2 ^ D

Inv ==
    Sum(i \in 1..N : towers[i]) = AllDisks

====