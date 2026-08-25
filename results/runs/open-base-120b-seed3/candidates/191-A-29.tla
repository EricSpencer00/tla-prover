---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskSet == { 2^i : i \in 0..(D-1) }          \* all disks, each a power of two
AllDisks == 2^D - 1                         \* sum of all disks

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsOn(t, d) == ((t \div d) % 2) = 1           \* true iff disk d (a power of two) is present in tower value t
SmallestOn(t, d) == IsOn(t, d) /\ (t % d = 0) \* d is the smallest disk on tower t
NoSmaller(t, d) == (t % d = 0)               \* tower t has no disk smaller than d (or is empty)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

\* ----------------------------------------------------------------------
\* Next-state relation (a legal move)
\* ----------------------------------------------------------------------
Move(s, t, d) ==
    /\ s # t
    /\ d \in DiskSet
    /\ SmallestOn(towers[s], d)          \* d is present on source and is the smallest there
    /\ NoSmaller(towers[t], d)           \* destination has no smaller disk
    /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                 ![t] = towers[t] + d]

Next ==
    \E s \in 1..N: \E t \in 1..N: Move(s, t, d)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

Inv ==
    /\ \Sum i \in 1..N: towers[i] = AllDisks

====