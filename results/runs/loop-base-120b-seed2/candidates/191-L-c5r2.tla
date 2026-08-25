---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Integers

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* State variable: an array (function) mapping each tower index to a
\* natural number encoding the disks present on that tower.
\* ----------------------------------------------------------------------
VARIABLES Tower

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskSet == { 2 ^ k : k \in 0..(D-1) }

AllDisksValue == 2 ^ D - 1

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Is disk d present on tower t ?
Present(t, d) == ((t \div d) % 2) = 1

\* Is d the smallest disk on tower t ? (i.e., no smaller disk present)
Smallest(t, d) == (t % d) = 0

\* ----------------------------------------------------------------------
\* Initial state: all disks on tower 1, others empty
\* ----------------------------------------------------------------------
Init ==
    Tower = [i \in 1..N |-> IF i = 1 THEN AllDisksValue ELSE 0]

\* ----------------------------------------------------------------------
\* One legal move
\* ----------------------------------------------------------------------
Move ==
    \E src, dst \in 1..N :
        /\ src # dst
        /\ \E d \in DiskSet :
            /\ Present(Tower[src], d)          \* disk d is on source
            /\ Smallest(Tower[src], d)         \* it is the smallest on source
            /\ Smallest(Tower[dst], d)         \* destination has no smaller disk
            /\ Tower' = [Tower EXCEPT ![src] = Tower[src] - d,
                                      ![dst] = Tower[dst] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Tower>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Tower \in [1..N -> Nat]
    /\ \A i \in 1..N : Tower[i] < 2 ^ D

Inv ==
    Sum({ Tower[i] : i \in 1..N }) = AllDisksValue

====