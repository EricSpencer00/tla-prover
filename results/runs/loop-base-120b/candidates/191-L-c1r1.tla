---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Set of all disk values (powers of two) *)
DiskSet == { 2 ^ k : k \in 0..D-1 }

(* Bit‑wise helpers expressed arithmetically *)
DiskOn(t, d) == (t % (2 * d)) >= d
SmallestOn(t, d) == (t % d) = 0

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

Next ==
    \E d \in DiskSet :
        \E src \in 1..N :
            \E dst \in 1..N :
                /\ src # dst
                /\ DiskOn(towers[src], d)
                /\ SmallestOn(towers[src], d)
                /\ SmallestOn(towers[dst], d)
                /\ towers' = [i \in 1..N |->
                                 IF i = src THEN towers[i] - d
                                 ELSE IF i = dst THEN towers[i] + d
                                 ELSE towers[i]]

Spec == Init /\ [][Next]_towers

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv ==
    (+/ i \in (1..N) : towers[i]) = (2 ^ D) - 1

====