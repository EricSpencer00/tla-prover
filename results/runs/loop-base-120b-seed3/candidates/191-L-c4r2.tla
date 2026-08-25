---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Arithmetic

CONSTANTS D, N

VARIABLES towers

(* --- derived constants --- *)
DiskSet == { 2 ^ i : i \in 0..D-1 }
FullMask == 2 ^ D - 1

(* --- type correctness --- *)
TypeOK == /\ towers \in [1..N -> Nat]
          /\ \A i \in 1..N : towers[i] \in 0..FullMask

(* --- initial state --- *)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN FullMask ELSE 0]
        /\ TypeOK

(* --- helper predicates --- *)
DiskPresent(t, d) == (t \div d) % 2 = 1
SmallestOn(t, d) == t % d = 0

(* --- move action --- *)
Move ==
  \E d \in DiskSet:
    \E src \in 1..N:
      \E dst \in 1..N:
        /\ src # dst
        /\ DiskPresent(towers[src], d)          \* the disk is on the source tower
        /\ SmallestOn(towers[src], d)           \* it is the smallest on source
        /\ SmallestOn(towers[dst], d)           \* destination has no smaller disk
        /\ towers' = [towers EXCEPT
                        ![src] = towers[src] - d,
                        ![dst] = towers[dst] + d]

Next == Move

(* --- specification --- *)
Spec == Init /\ [][Next]_towers

(* --- invariant (type + conservation) --- *)
Inv == /\ TypeOK
       /\ Sum(i \in 1..N, towers[i]) = FullMask

====