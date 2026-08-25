---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TowerRange == 1 .. N

DiskSet == { 2 ^ k : k \in 0 .. (D - 1) }

\* Test whether disk d (a power of two) is present on tower value t
DiskOn(t, d) == (t \div d) % 2 = 1

\* True iff d is the smallest disk present on tower value t
SmallestOn(t, d) ==
    DiskOn(t, d) /\ \A d2 \in DiskSet : d2 < d => (t \div d2) % 2 = 0

\* Destination tower must not contain any disk smaller than d
DestOk(t, d) == \A d2 \in DiskSet : d2 < d => (t \div d2) % 2 = 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers \in [TowerRange -> Nat]
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in TowerRange \ {1} : towers[i] = 0

\* ----------------------------------------------------------------------
\* Next-state relation (a legal move)
\* ----------------------------------------------------------------------
Move(d, src, dst) ==
    /\ src # dst
    /\ d \in DiskSet
    /\ DiskOn(towers[src], d)
    /\ SmallestOn(towers[src], d)
    /\ DestOk(towers[dst], d)
    /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                              ![dst] = towers[dst] + d]

Next ==
    \E src \in TowerRange, dst \in TowerRange :
        \E d \in DiskSet :
            Move(d, src, dst)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_towers

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [TowerRange -> Nat]
    /\ \A i \in TowerRange : towers[i] < (2 ^ D)

Inv ==
    LET total == Sum({ towers[i] : i \in TowerRange })
    IN total = (2 ^ D) - 1

=============================================================================