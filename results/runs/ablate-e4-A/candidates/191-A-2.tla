---- MODULE Hanoi ----
EXTENDS Integers, FiniteSets

CONSTANTS D, N

VARIABLE towers

(* The set of disk values, each a distinct power of two *)
DiskValues == { 2^k : k \in 0 .. D-1 }

(* Initial state: all disks on tower 1, others empty *)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2^D - 1) ELSE 0]

(* Helper: a disk is present on a tower and there are no smaller disks on that tower *)
TopDisk(disk, towerVal) ==
    (towerVal & disk) = disk /\ (towerVal & (disk - 1)) = 0

(* Helper: the destination tower has no smaller disk than the one being moved *)
ClearBelow(disk, towerVal) ==
    (towerVal & (disk - 1)) = 0

(* Move action: choose source, destination, and disk satisfying the puzzle constraints *)
Move ==
    \E src \in 1..N, dest \in 1..N, disk \in DiskValues :
        src # dest
        /\ TopDisk(disk, towers[src])
        /\ ClearBelow(disk, towers[dest])
        /\ towers' = [t \in 1..N |-> 
                       IF t = src THEN towers[src] - disk
                       ELSE IF t = dest THEN towers[dest] + disk
                       ELSE towers[t]]

Next == Move

Spec == Init /\ [][Next]_towers

(* Invariant: each tower value is a natural number less than 2^D *)
TypeOK == \A t \in 1..N : towers[t] \in 0 .. (2^D - 1)

(* Invariant: the sum of all tower values always equals the total disk value *)
Inv == \Sum t \in 1..N : towers[t] = 2^D - 1

====