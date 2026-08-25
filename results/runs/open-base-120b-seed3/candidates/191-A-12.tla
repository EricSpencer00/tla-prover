---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES towers

(* Set of disk values, each a distinct power of two *)
Disk == { 2 ^ i : i \in 0..D-1 }

(* Initial configuration: all disks on the first tower *)
Init ==
    /\ towers[1] = 2 ^ D - 1
    /\ \A i \in 2..N: towers[i] = 0

(* Helper predicates for bitwise reasoning *)
IsOn(t, d) == (t \div d) % 2 = 1
IsSmallest(t, d) == IsOn(t, d) /\ (t % d) = 0
DestOk(t, d) == (t % d) = 0

(* One legal move *)
Move ==
    \E d \in Disk:
        \E s, t \in 1..N:
            /\ s # t
            /\ IsSmallest(towers[s], d)
            /\ DestOk(towers[t], d)
            /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                        ![t] = towers[t] + d]

Next == Move

Spec == Init /\ [] [Next]_<<towers>>

(* Type correctness: each tower value is a natural < 2^D *)
TypeOK == \A i \in 1..N: towers[i] \in Nat /\ towers[i] < 2 ^ D

(* Conservation: total sum of bits equals 2^D - 1 *)
Inv == \Sum i \in 1..N: towers[i] = 2 ^ D - 1
====