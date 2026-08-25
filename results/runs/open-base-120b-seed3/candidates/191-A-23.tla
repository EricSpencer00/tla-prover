---- MODULE Hanoi ----
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxMask == 2^D - 1

Disk(i) == 2^i           \* Disk of size 2^i, i \in 0..D-1
DiskSet == { Disk(i) : i \in 0..(D-1) }

DiskOn(t, d) == ((t \div d) % 2) = 1

SmallestDisk(t, d) ==
    DiskOn(t, d) /\ \A e \in DiskSet : (e < d) => ~DiskOn(t, e)

DestOk(t, d) ==
    \A e \in DiskSet : (e < d) => ~DiskOn(t, e)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* ----------------------------------------------------------------------
\* Initial state: all disks on tower 1
\* ----------------------------------------------------------------------
Init ==
    /\ towers[1] = MaxMask
    /\ \A i \in 2..N: towers[i] = 0

\* ----------------------------------------------------------------------
\* Next-state relation: a legal move of the smallest disk on a source
\* tower to a destination tower that has no smaller disk.
\* ----------------------------------------------------------------------
Move ==
    \E src \in 1..N, dst \in 1..N :
        /\ src # dst
        /\ \E d \in DiskSet :
            /\ DiskOn(towers[src], d)
            /\ SmallestDisk(towers[src], d)
            /\ DestOk(towers[dst], d)
            /\ towers' = [towers EXCEPT
                            ![src] = towers[src] - d,
                            ![dst] = towers[dst] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<towers>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in 0..MaxMask

Inv ==
    (\sum i \in 1..N: towers[i]) = MaxMask

=============================================================================