---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N \* number of disks and towers

\* ----------------------------------------------------------------------
\* State variable: towers[t] is the bitwise encoding of the disks on tower t
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Disk(i) == 2 ^ i                      \* size of disk i (i = 0 .. D-1)

\* The set of all possible tower values (all subsets of disks)
TowerVals == 0 .. (2 ^ D - 1)

\* ----------------------------------------------------------------------
\* Initial state: all disks on the first tower
\* ----------------------------------------------------------------------
Init ==
    /\ towers \in [1..N -> TowerVals]
    /\ towers[1] = 2 ^ D - 1
    /\ \A t \in 2..N: towers[t] = 0

\* ----------------------------------------------------------------------
\* Type correctness: each tower value is a natural < 2^D
\* ----------------------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> TowerVals]

\* ----------------------------------------------------------------------
\* Invariant: conservation of all disks
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ (+/ t \in 1..N : towers[t]) = 2 ^ D - 1

\* ----------------------------------------------------------------------
\* Move action: pick a disk, a source tower and a destination tower
\* ----------------------------------------------------------------------
Move ==
    \E i \in 0..D-1:
        \E s \in 1..N:
            \E d \in 1..N:
                /\ s # d
                LET disk == Disk(i) IN
                    /\ (towers[s] % (2 * disk)) = disk      \* disk is present and is the smallest on source
                    /\ (towers[d] % (2 * disk)) = 0          \* destination has no smaller disk
                    /\ towers' = [t \in 1..N |->
                                    IF t = s THEN towers[s] - disk
                                    ELSE IF t = d THEN towers[d] + disk
                                    ELSE towers[t]]

\* ----------------------------------------------------------------------
\* Next-state relation (nondeterministic move or stutter)
\* ----------------------------------------------------------------------
Next == Move \/ UNCHANGED towers

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* CONSTANTS: D, N          (declared above)
\* SPECIFICATION: Spec
\* INVARIANTS: TypeOK, Inv
\* ----------------------------------------------------------------------

====