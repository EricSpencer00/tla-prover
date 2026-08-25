---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLE tower

\* --- Derived constants ---
AllDisks == 2 ^ D - 1
Disks == { 2 ^ k : k \in 0..D-1 }

\* --- Helper predicates ---
DiskPresent(t, d) == ((t \div d) % 2) = 1
SmallestOn(t, d) == DiskPresent(t, d) /\ (t % d) = 0
NoSmaller(t, d) == (t % d) = 0

\* --- Initial state ---
Init ==
    tower = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

\* --- One legal move ---
Move ==
    \E s, r \in 1..N :
        /\ s # r
        /\ \E d \in Disks :
            /\ SmallestOn(tower[s], d)
            /\ NoSmaller(tower[r], d)
            /\ tower' = [tower EXCEPT ![s] = tower[s] - d,
                                       ![r] = tower[r] + d]

\* --- Next-state relation ---
Next == Move

\* --- Type correctness invariant ---
TypeOK ==
    /\ tower \in [1..N -> Nat]
    /\ \A i \in 1..N : tower[i] < 2 ^ D

\* --- Conservation invariant ---
Inv ==
    \Sum i \in 1..N : tower[i] = AllDisks

\* --- Specification ---
Spec == Init /\ [][Next]_tower

====