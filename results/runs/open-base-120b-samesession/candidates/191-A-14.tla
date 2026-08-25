---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Disk sizes are powers of two: 1,2,4,...,2^(D-1) *)
Disk(i) == 2^(i - 1)
DiskVals == { Disk(i) : i \in 1..D }

(* Bit‑wise helpers expressed arithmetically *)
IsSet(v, d) == (v \div d) % 2 = 1
NoSmaller(v, d) == v % d = 0
SmallestOn(v, d) == IsSet(v, d) /\ NoSmaller(v, d)

(* Initial state: all disks on tower 1 *)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
    /\ TypeOK

(* Type correctness: each tower value is a natural < 2^D *)
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2^D

(* Invariant: conservation of total disk weight and type correctness *)
Inv ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2^D
    /\ Sum(i \in 1..N: towers[i]) = 2^D - 1

(* One legal move *)
Move ==
    \E d \in DiskVals:
        \E s, t \in 1..N:
            /\ s # t
            /\ SmallestOn(towers[s], d)        \* d is the smallest disk on source
            /\ NoSmaller(towers[t], d)          \* destination has no smaller disk
            /\ towers' = [i \in 1..N |
                    IF i = s THEN towers[i] - d
                    ELSE IF i = t THEN towers[i] + d
                    ELSE towers[i]]

Next == Move

Spec == Init /\ [][Next]_towers

====