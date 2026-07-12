---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
\* The set of all disk values (powers of two)
DiskValues == { 2^k : k \in 0..(D-1) }

\* The maximum tower value (all disks on one tower)
MaxTowerVal == 2^D - 1

\* ----------------------------------------------------------------------
\* State variable: an array of N tower values
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of tower indices
TowerIdx == 1..N

\* The set of all possible tower values (0..MaxTowerVal)
TowerVals == 0..MaxTowerVal

\* Test whether a disk value is present in a tower value
HasDisk(towerVal, disk) == (towerVal /\ disk) = disk

\* Test whether a tower value has any smaller disk than the given disk
HasSmaller(towerVal, disk) ==
    \E d \in DiskValues : d < disk /\ HasDisk(towerVal, d)

\* The smallest disk present on a tower (if any)
SmallestDisk(towerVal) ==
    IF towerVal = 0 THEN 0
    ELSE
        \E d \in DiskValues : HasDisk(towerVal, d) /\ \A d' \in DiskValues :
            (d' < d) => ~HasDisk(towerVal, d')

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ towers = [i \in TowerIdx |-> IF i = 1 THEN MaxTowerVal ELSE 0]

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
    \E src, dst \in TowerIdx :
        /\ src # dst
        /\ \E disk \in DiskValues :
            /\ HasDisk(towers[src], disk)
            /\ (SmallestDisk(towers[src]) = disk)
            /\ (towers[dst] = 0 \/ ~HasSmaller(towers[dst], disk))
            /\ towers' = [towers EXCEPT ![src] = towers[src] - disk,
                                      ![dst] = towers[dst] + disk]
        /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [TowerIdx -> TowerVals]
    /\ \A i \in TowerIdx : towers[i] <= MaxTowerVal

\* ----------------------------------------------------------------------
\* Conservation invariant (sum of tower values equals MaxTowerVal)
\* ----------------------------------------------------------------------
Inv ==
    \A i \in TowerIdx : towers[i] \in TowerVals
    /\ Sum(towers) = MaxTowerVal

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====