---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES towers

(* Disk size as a power of two, indexed from 0 to D-1 *)
Disk(k) == 2 ^ k

(* Helper predicates for bitwise reasoning using arithmetic *)
IsOn(t, d) == (t % (2 * d)) >= d
IsSmallest(t, d) == IsOn(t, d) /\ (t % d) = 0

AllDisksSum == 2 ^ D - 1

Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisksSum
    /\ \A i \in 2..N : towers[i] = 0
    /\ \A i \in 1..N : towers[i] < 2 ^ D

Next ==
    \E src \in 1..N, dst \in 1..N, k \in 0..(D - 1) :
        /\ src # dst
        /\ LET d == Disk(k) IN
            /\ IsSmallest(towers[src], d)          \* disk is present and smallest on source
            /\ (towers[dst] % d) = 0               \* no smaller disk on destination
            /\ towers' = [i \in 1..N |-> 
                            IF i = src THEN towers[i] - d
                            ELSE IF i = dst THEN towers[i] + d
                            ELSE towers[i]]

Spec == Init /\ [][Next]_towers

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv ==
    /\ \Sum i \in 1..N : towers[i] = AllDisksSum

====