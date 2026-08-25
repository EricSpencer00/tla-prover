---- MODULE Hanoi ----
EXTEND Naturals, FiniteSets

CONSTANT D, N

VARIABLE towers

(*--- Disk set: powers of two representing each disk ---*)
DiskSet == { 2^i : i \in 0..D-1 }

(*--- Helper predicates ---*)
IsOn(t, d) == ((t \div d) % 2) = 1
SmallestOn(t, d) == (t % d) = 0

(*--- Initial state: all disks on tower 1 ---*)
Init ==
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--- Next-state relation: one legal move ---*)
Next ==
    \E d \in DiskSet:
      \E src, dst \in 1..N:
        /\ src # dst
        /\ IsOn(towers[src], d)                \* disk d is on source tower
        /\ SmallestOn(towers[src], d)          \* d is the smallest disk on src
        /\ SmallestOn(towers[dst], d)          \* no smaller disk on dst
        /\ towers' = [i \in 1..N |->
                        IF i = src THEN towers[i] - d
                        ELSE IF i = dst THEN towers[i] + d
                        ELSE towers[i]]

(*--- Type correctness: each tower value is a natural less than 2^D ---*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] \in 0..(2^D - 1)

(*--- Invariant: conservation of all disks ---*)
Inv ==
    /\ TypeOK
    /\ (\Sum i \in 1..N: towers[i]) = 2^D - 1

(*--- Specification ---*)
Spec ==
    Init /\ [][Next]_towers

====