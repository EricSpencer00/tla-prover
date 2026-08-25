---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Set of disks, each represented by a distinct power of two *)
DiskSet == { 2^i : i \in 0..D-1 }

(* Disk d is present in tower value t iff the corresponding bit is set *)
Contains(t, d) == ((t \div d) % 2) = 1

(* Smallest disk on tower t (0 if the tower is empty) *)
Smallest(t) ==
    IF t = 0 THEN 0
    ELSE CHOOSE d \in DiskSet :
            Contains(t, d) /\ \A e \in DiskSet : (e < d) => ~Contains(t, e)

(* No disk smaller than d is present on tower t *)
NoSmaller(t, d) == \A e \in DiskSet : e < d => ~Contains(t, e)

Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N : towers[i] = 0
    /\ TypeOK

Next ==
    \E d \in DiskSet :
      \E src \in 1..N :
        \E dst \in 1..N :
          /\ src # dst
          /\ Contains(towers[src], d)
          /\ d = Smallest(towers[src])
          /\ NoSmaller(towers[dst], d)
          /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

TypeOK ==
    \A i \in 1..N : towers[i] \in 0..(2^D - 1)

Inv ==
    /\ TypeOK
    /\ \Sum i \in 1..N : towers[i] = 2^D - 1

Spec ==
    Init /\ [][Next]_towers

====