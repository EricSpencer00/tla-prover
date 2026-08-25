---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANT D, N

VARIABLES towers

\* --- Derived definitions -------------------------------------------------
AllDisks == 2^D - 1

DiskSet == { 2^(i - 1) : i \in 1..D }

\* Disk d is the smallest disk on tower value v
SmallestOn(v, d) == 
    /\ (v % (2 * d) >= d)   \* d is present (bit d set)
    /\ (v % d = 0)          \* no smaller bits are set

\* --- Initial state -------------------------------------------------------
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisks
    /\ \A i \in (1..N) \ {1} : towers[i] = 0

\* --- Move action ---------------------------------------------------------
Move ==
    \E d \in DiskSet, s \in 1..N, t \in 1..N :
        /\ s # t
        /\ SmallestOn(towers[s], d)            \* d is smallest on source
        /\ (towers[t] % d = 0)                 \* destination has no smaller disk
        /\ towers' = [towers EXCEPT 
                        ![s] = towers[s] - d,
                        ![t] = towers[t] + d]

\* --- Next-state relation -------------------------------------------------
Next == Move

\* --- Specification --------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* --- Invariants -----------------------------------------------------------
TypeOK == 
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2^D

Inv == 
    /\ Sum(i \in 1..N: towers[i]) = AllDisks

=============================================================================