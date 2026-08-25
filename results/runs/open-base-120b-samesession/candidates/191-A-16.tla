---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
DiskValues == { 2 ^ (i - 1) : i \in 1..D }

IsOn(t, d) == ((t \div d) % 2) = 1

NoSmallerOn(t, d) == \A e \in DiskValues : (e < d) => ~IsOn(t, e)

\* -------------------------------------------------
\* State variable
\* -------------------------------------------------
VARIABLES towers

\* -------------------------------------------------
\* Initial state: all disks on tower 1
\* -------------------------------------------------
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* -------------------------------------------------
\* Move action
\* -------------------------------------------------
Move ==
    \E src, dst \in 1..N :
    \E d \in DiskValues :
        /\ src # dst
        /\ IsOn(towers[src], d)                 \* disk is on source
        /\ NoSmallerOn(towers[src], d)          \* it is the smallest on source
        /\ NoSmallerOn(towers[dst], d)          \* destination has no smaller disk
        /\ towers' = [towers EXCEPT
                        ![src] = towers[src] - d,
                        ![dst] = towers[dst] + d]

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next == Move

\* -------------------------------------------------
\* Type correctness invariant
\* -------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < (2 ^ D)

\* -------------------------------------------------
\* Conservation invariant (sum of disks stays constant)
\* -------------------------------------------------
Inv ==
    /\ TypeOK
    /\ \Sum i \in 1..N : towers[i] = (2 ^ D) - 1

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_towers

====