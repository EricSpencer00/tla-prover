---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, Bitwise

CONSTANTS D, N

VARIABLES towers

(* Set of all possible disk values: powers of two up to 2^(D-1) *)
DiskSet == { 2 ^ k : k \in 0..(D-1) }

(* Initial state: all disks on the first tower *)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

(* Disk d is the smallest (top) disk on tower value t *)
IsSmallest(t, d) ==
    /\ BAnd(t, d) = d
    /\ BAnd(t, d - 1) = 0

(* Disk d can be placed on tower value t (no smaller disk present) *)
CanPlace(t, d) ==
    BAnd(t, d - 1) = 0

(* A legal move of disk d from src to dst *)
Move(d, src, dst) ==
    /\ d \in DiskSet
    /\ src \in 1..N
    /\ dst \in 1..N
    /\ src # dst
    /\ IsSmallest(towers[src], d)
    /\ CanPlace(towers[dst], d)

(* One-step transition relation *)
Next ==
    \E d, src, dst :
        Move(d, src, dst) /\
        towers' = [i \in 1..N |
                    IF i = src THEN towers[i] - d
                    ELSE IF i = dst THEN towers[i] + d
                    ELSE towers[i]]

(* The full specification *)
Spec ==
    Init /\ [][Next]_towers

(* Type-correctness invariant *)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..((2 ^ D) - 1)

(* Conservation invariant *)
Inv ==
    \Sum i \in 1..N : towers[i] = (2 ^ D) - 1

====