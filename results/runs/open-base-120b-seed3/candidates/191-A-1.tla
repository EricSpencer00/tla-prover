---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

(*--- Set of disks, each represented by a distinct power of two ---*)
DiskSet == { 2 ^ i : i \in 0..(D - 1) }

(*--- Helper predicates using arithmetic to mimic bitwise tests ---*)
DiskOn(t, d) == (t % (2 * d) >= d)               \* disk d is present on tower t
SmallestOn(t, d) == DiskOn(t, d) /\ (t % d = 0)  \* d is the smallest disk on t
DestOK(t, d) == (t % d = 0)                       \* no smaller disk on destination

(*--- Initial state: all disks on tower 1, others empty ---*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in 2..N: towers[i] = 0
    /\ TypeOK

(*--- One legal move ---*)
Move ==
    \E d \in DiskSet:
      \E s \in 1..N:
        \E t \in 1..N:
          /\ s # t
          /\ SmallestOn(towers[s], d)   \* d is the top disk on source
          /\ DestOK(towers[t], d)       \* destination can receive d
          /\ towers' = [towers EXCEPT
                          ![s] = towers[s] - d,
                          ![t] = towers[t] + d]

Next == Move

Spec == Init /\ [][Next]_towers

(*--- Type correctness invariant ---*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < (2 ^ D)

(*--- Safety invariant: total number of disks is conserved ---*)
Inv ==
    /\ \Sum i \in 1..N: towers[i] = (2 ^ D) - 1

====