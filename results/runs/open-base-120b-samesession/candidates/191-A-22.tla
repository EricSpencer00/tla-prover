---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES towers

(* Set of disk values, each a distinct power of two *)
Disk == { 2^k : k \in 0..D-1 }

(* Helper predicates using arithmetic to emulate bitwise tests *)
DiskOn(t, d) == (t % (2 * d) >= d)               \* disk d is present on tower t
SmallestOn(t, d) == DiskOn(t, d) /\ (t % d = 0)  \* d is the smallest disk on t
DestOk(t, d) == (t % d = 0)                      \* no smaller disk on destination

(* Initial state: all disks on the first tower *)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(* One legal move *)
Move ==
    \E i, j \in 1..N: i # j /\
        \E d \in Disk:
            /\ SmallestOn(towers[i], d)
            /\ DestOk(towers[j], d)
            /\ towers' = [towers EXCEPT ![i] = towers[i] - d,
                                         ![j] = towers[j] + d]

Next == Move

(* Type correctness: each tower value is a natural < 2^D *)
TypeOK ==
    \A i \in 1..N: towers[i] \in Nat /\ towers[i] < 2^D

(* Conservation invariant: total of all disks is constant *)
Inv ==
    (+/ i \in 1..N: towers[i]) = 2^D - 1

(* Full specification *)
Spec ==
    Init /\ [][Next]_<<towers>>

====