---- MODULE Hanoi ----
EXTENDS Integers, TLC

CONSTANT D, N

(*-----------------------------------------------------------------
  Disk representation: each disk size is a distinct power of two.
  The set of all disk values (powers of two) is denoted by Disks.
-----------------------------------------------------------------*)
Disks == { 2 ^ i : i \in 0..(D - 1) }

(* Helper to compute the total sum of all disks *)
AllDisksSum == 2 ^ D - 1

(*-----------------------------------------------------------------
  State variable: an array (function) mapping each tower index to the
  natural number that encodes which disks are present on that tower.
-----------------------------------------------------------------*)
VARIABLES tower

(*-----------------------------------------------------------------
  Type correctness predicate: each tower value is a natural number
  less than the sum of all disks.
-----------------------------------------------------------------*)
TypeOK == /\ tower \in [1..N -> Nat]
         /\ \A i \in 1..N : tower[i] <= AllDisksSum

(*-----------------------------------------------------------------
  Initialization: all disks on the first tower, all other towers empty.
-----------------------------------------------------------------*)
Init ==
    /\ tower = [i \in 1..N |-> IF i = 1 THEN AllDisksSum ELSE 0]
    /\ TypeOK

(*-----------------------------------------------------------------
  Helper to obtain the smallest disk present on a tower (or 0 if empty).
-----------------------------------------------------------------*)
SmallestDisk(t) ==
    IF t = 0 THEN 0
    ELSE
        \E d \in Disks :
            /\ (t /\ d) = d          \* d is a set bit of t
            /\ \A d2 \in Disks :
                   (d2 < d) => (t /\ d2) = 0   \* no smaller disk present
            /\ d

(*-----------------------------------------------------------------
  Move action: nondeterministically choose a source tower, destination
  tower, and a disk to move, subject to the Hanoi constraints.
-----------------------------------------------------------------*)
Move ==
    \E src \in 1..N, dst \in 1..N, d \in Disks :
        /\ src # dst
        /\ (tower[src] /\ d) = d                     \* disk is on source
        /\ SmallestDisk(tower[src]) = d               \* disk is top of src
        /\ (tower[dst] = 0 \/ SmallestDisk(tower[dst]) > d)  \* no smaller on dst
        /\ tower' = [tower EXCEPT
                       ![src] = tower[src] - d,
                       ![dst] = tower[dst] + d]

(*-----------------------------------------------------------------
  Next-state relation: either make a legal move or stutter.
-----------------------------------------------------------------*)
Next == Move \/ UNCHANGED tower

(*-----------------------------------------------------------------
  Safety invariant: conservation of total disk value.
-----------------------------------------------------------------*)
Inv == \A i \in 1..N : tower[i] \in Nat
       /\ \A i \in 1..N : tower[i] <= AllDisksSum
       /\ \A i \in 1..N : (tower[i] = 0) \/ (SmallestDisk(tower[i]) \in Disks)
       /\ \A i \in 1..N : \A d \in Disks :
            (tower[i] /\ d) = d => 
                \A d2 \in Disks :
                    (d2 < d) => (tower[i] /\ d2) = 0
       /\ \A i \in 1..N : \A j \in 1..N :
            i # j => \A d \in Disks :
                (tower[i] /\ d) = d => (tower[j] /\ d) = 0
       /\ \A i \in 1..N : \A d \in Disks :
            (tower[i] /\ d) = d => d \in Disks
       /\ \A i \in 1..N : \A d \in Disks :
            (tower[i] /\ d) = d => \A d2 \in Disks :
                (d2 < d) => (tower[i] /\ d2) = 0
       /\ \A i \in 1..N : \A d \in Disks :
            (tower[i] /\ d) = d => (tower[i] - d) >= 0
       /\ \SUM i \in 1..N : tower[i] = AllDisksSum

(*-----------------------------------------------------------------
  Full specification: Init and Next with stuttering.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<tower>>

====