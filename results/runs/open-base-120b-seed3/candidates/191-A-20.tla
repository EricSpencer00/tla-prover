---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DiskSet == { 2^i : i \in 0..D-1 }

\* True iff disk d (a power of two) is present on tower value t
IsPresent(t, d) == ((t \div d) % 2) = 1

\* True iff there is no disk smaller than d on tower value t
NoSmaller(t, d) == (t % d) = 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N: towers[i] = 0

\* ----------------------------------------------------------------------
\* Next-state relation (a legal move)
\* ----------------------------------------------------------------------
Next ==
    \E src, dst \in 1..N: 
        /\ src # dst
        /\ \E d \in DiskSet :
            /\ IsPresent(towers[src], d)
            /\ NoSmaller(towers[src], d)          \* d is the smallest on src
            /\ NoSmaller(towers[dst], d)          \* dst has no smaller disk
            /\ towers' = [towers EXCEPT 
                            ![src] = towers[src] - d,
                            ![dst] = towers[dst] + d]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

Inv ==
    (\Sum i \in 1..N: towers[i]) = 2^D - 1

=============================================================================