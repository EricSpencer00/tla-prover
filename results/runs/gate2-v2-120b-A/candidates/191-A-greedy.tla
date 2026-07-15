---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

\* Disk values are powers of two: 1, 2, 4, ..., 2^(D-1)
DiskSet == { 2 ^ i : i \in 0..(D - 1) }

\* The maximum value representing all disks present
AllDisks == 2 ^ D - 1

\* Tower indices
Towers == 1..N

VARIABLES towers

\* towers[t] is the natural number encoding the set of disks on tower t
\* Initially all disks are on tower 1, others empty
Init ==
    /\ towers = [t \in Towers |-> IF t = 1 THEN AllDisks ELSE 0]
    /\ \A t \in Towers: towers[t] \in 0..AllDisks

\* Helper: the smallest disk present on a tower (or 0 if empty)
SmallestDisk(t) ==
    IF towers[t] = 0 THEN 0
    ELSE
        \E d \in DiskSet :
            /\ (towers[t] /\ d) = d          \* disk d is present
            /\ \A d2 \in DiskSet :
                (d2 < d) => (towers[t] /\ d2) = 0
            /\ d

\* Helper: the set of disks present on a tower (as a set of powers of two)
DisksOn(t) ==
    { d \in DiskSet : (towers[t] /\ d) = d }

\* A move selects a source tower, a destination tower, and a disk d
Move ==
    \E src \in Towers, dst \in Towers, d \in DiskSet :
        /\ src # dst
        /\ (towers[src] /\ d) = d                     \* d is on src
        /\ \A d2 \in DiskSet :
               (d2 < d) => (towers[src] /\ d2) = 0    \* d is smallest on src
        /\ (towers[dst] = 0 \/ \A d2 \in DiskSet :
               (d2 < d) => (towers[dst] /\ d2) = 0)   \* dst empty or no smaller disk
        /\ towers' = [t \in Towers |-> 
               IF t = src THEN towers[t] - d
               ELSE IF t = dst THEN towers[t] + d
               ELSE towers[t]]

Next == Move

\* Safety invariant: conservation of total disk value
Inv == 
    /\ \A t \in Towers: towers[t] \in 0..AllDisks
    /\ \A t \in Towers: towers[t] = 0 \/ 
          \E d \in DiskSet : (towers[t] /\ d) = d
    /\ \A t \in Towers: 
          \A d \in DiskSet :
              (towers[t] /\ d) = d => 
                 \A d2 \in DiskSet :
                     (d2 < d) => (towers[t] /\ d2) = 0
    /\ \Sum_{t \in Towers} towers[t] = AllDisks

\* Type correctness: each tower value is a natural number less than 2^D
TypeOK == 
    /\ \A t \in Towers: towers[t] \in Nat
    /\ \A t \in Towers: towers[t] < 2 ^ D

\* Full specification
Spec == Init /\ [][Next]_<<towers>>

\* The specification name required by the .cfg file
Spec == Spec

====