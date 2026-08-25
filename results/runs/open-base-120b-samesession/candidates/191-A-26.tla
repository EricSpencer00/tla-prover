---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--- Disk set: each disk is a power of two ---*)
DiskSet == { 2 ^ i : i \in 0..D-1 }

(*--- Initial state: all disks on the first tower ---*)
Init ==
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--- Type correctness: towers are natural numbers within bounds ---*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] \in 0..(2 ^ D) - 1

(*--- Helper to sum all tower values ---*)
SumTowers(t) == Sum({ t[i] : i \in 1..N })

(*--- Global invariant: type correctness and conservation of disks ---*)
Inv ==
    /\ TypeOK
    /\ SumTowers(towers) = (2 ^ D) - 1

(*--- Bitwise‑style predicates expressed arithmetically ---*)
DiskOn(t, d) == (t % (2 * d)) >= d
SmallestOn(t, d) == DiskOn(t, d) /\ (t % d) = 0
NoSmallerOn(t, d) == (t % d) = 0

(*--- A legal move of disk d from src to dst ---*)
Move(d, src, dst) ==
    /\ d \in DiskSet
    /\ src \in 1..N
    /\ dst \in 1..N
    /\ src # dst
    /\ SmallestOn(towers[src], d)
    /\ NoSmallerOn(towers[dst], d)
    /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                 ![dst] = towers[dst] + d]

(*--- Next-state relation: any legal move ---*)
Next ==
    \E d \in DiskSet: \E src, dst \in 1..N: src # dst /\ Move(d, src, dst)

(*--- Specification of the system ---*)
Spec ==
    Init /\ [][Next]_towers

====