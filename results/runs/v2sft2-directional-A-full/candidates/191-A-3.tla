---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS D, N \* number of disks, number of towers

\* Types
DISK == 1 .. 2^(D-1)               \* disk values (powers of two)
TOWER == 1 .. N                    \* tower identifiers

\* Helper definitions
BitMask == 1 .. 2^(D-1)             \* same as DISK, used for bit tests

\* DiskSet is the set of all possible disk values
DiskSet == {2^k : k \in 0 .. D-1}

\* Initial tower configuration: all disks on tower 1
Init ==
    \E towers \in [TOWER -> Nat] :
        /\ towers[1] = 2^D - 1
        /\ \A i \in 2 .. N : towers[i] = 0

\* Type correctness: each tower state is a natural number < 2^D
TypeOK ==
    \A i \in TOWER : towers[i] \in 0 .. 2^D - 1

\* Utility: the set of disks present on a tower
Disks(tow) == \{ d \in DiskSet : tow \# d \}

\* Safety invariant: the total number of disks is always conserved
Inv ==
    \A i \in TOWER : towers[i] \in 0 .. 2^D - 1
    /\ \sum i \in TOWER : towers[i] = 2^D - 1

\* Move action: move the smallest disk from src to dst
Move ==
    \E src, dst \in TOWER :
        /\ src # dst
        /\ \E d \in DiskSet :
            /\ d \in Disks(towers[src])     \* disk is on src
            /\ d = Min(Disks(towers[src])) \* smallest on src
            /\ (towers[dst] = 0) \/ \A d2 \in DiskSet :
                d2 \in Disks(towers[dst]) => d2 > d
            /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                            ![dst] = towers[dst] + d]
            /\ UNCHANGED << >>

\* Next-state relation
NEXT ==
    Move

\* Specification
Spec ==
    Init /\ [][NEXT]_<<towers>>

====