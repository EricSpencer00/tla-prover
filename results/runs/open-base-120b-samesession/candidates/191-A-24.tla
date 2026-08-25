---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES Towers

(*--- Disk values are powers of two up to 2^(D-1) ---*)
DiskVals == { 2^k : k \in 0..D-1 }

(*--- true iff disk d is present on tower i ---*)
DiskPresent(d, i) == (Towers[i] % (2 * d)) >= d

(*--- Initial state: all disks on the first tower ---*)
Init ==
    Towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(*--- Type correctness: each tower value is a natural less than 2^D ---*)
TypeOK ==
    /\ Towers \in [1..N -> Nat]
    /\ \A i \in 1..N : Towers[i] < 2^D

(*--- Safety invariant: type correctness and conservation of disks ---*)
Inv ==
    /\ TypeOK
    /\ \Sum i \in 1..N : Towers[i] = 2^D - 1

(*--- One legal move ---*)
Next ==
    \E d \in DiskVals, s \in 1..N, t \in 1..N :
        /\ s # t
        /\ DiskPresent(d, s)                 \* disk d is on source tower
        /\ (Towers[s] % d) = 0                \* d is the smallest on source
        /\ (Towers[t] % d) = 0                \* destination has no smaller disk
        /\ Towers' = [Towers EXCEPT
                        ![s] = Towers[s] - d,
                        ![t] = Towers[t] + d]

(*--- Full specification ---*)
Spec == Init /\ [][Next]_Towers

====