---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Bitwise

CONSTANTS D, N

VARIABLES towers

(* Set of all disk values, each a distinct power of two *)
DiskSet == { 2^i : i \in 0..D-1 }

(* Disk d is present on tower value t *)
DiskOn(t, d) == And(t, d) = d

(* Disk d is the smallest disk on tower value t *)
SmallestOn(t, d) ==
    DiskOn(t, d) /\ 
    \A d2 \in DiskSet : d2 < d => And(t, d2) = 0

(* Destination tower dst may receive disk d (no smaller disk already there) *)
DestOk(dst, d) ==
    \A d2 \in DiskSet : d2 < d => And(towers[dst], d2) = 0

(* Initial configuration: all disks on the first tower *)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(* A legal move of the smallest disk d from src to dst *)
Next ==
    \E d \in DiskSet:
      \E src, dst \in 1..N:
        /\ src # dst
        /\ DiskOn(towers[src], d)
        /\ SmallestOn(towers[src], d)
        /\ DestOk(dst, d)
        /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                 ![dst] = towers[dst] + d]

(* Full behavior of the system *)
Spec == Init /\ [][Next]_<<towers>>

(* Type correctness: each tower value is a natural less than 2^D *)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

(* Conservation invariant: all disks are always accounted for *)
Inv ==
    /\ Sum(i \in 1..N: towers[i]) = 2^D - 1

====