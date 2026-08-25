---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS D, N

VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DiskSet == { 2 ^ i : i \in 0..(D - 1) }

\* Test if disk d (a power of two) is present on a tower value v
DiskPresent(v, d) == (v % (2 * d)) >= d

\* Test that no smaller disk than d is present on a tower value v
NoSmaller(v, d) == (v % d) = 0

\* Smallest disk on a tower: d is present and no smaller disk is present
SmallestOn(v, d) == DiskPresent(v, d) /\ NoSmaller(v, d)

\* Total number of disks (sum of all tower values)
Total == \Sum i \in 1..N: towers[i]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* ----------------------------------------------------------------------
\* Next-state relation (a legal move)
\* ----------------------------------------------------------------------
Next ==
    \E d \in DiskSet :
        \E s \in 1..N :
            \E t \in 1..N :
                /\ s # t
                /\ SmallestOn(towers[s], d)          \* d is the smallest on source
                /\ NoSmaller(towers[t], d)           \* destination has no smaller disk
                /\ towers' = [towers EXCEPT
                                ![s] = towers[s] - d,
                                ![t] = towers[t] + d]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < (2 ^ D)

Inv == Total = (2 ^ D) - 1

=============================================================================