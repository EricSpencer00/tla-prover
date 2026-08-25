---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Disk value for index i (1‑based) *)
Disk(i) == 2 ^ (i - 1)

DiskVals == { Disk(i) : i \in 1..D }

(* test whether bit d (a power of two) is set in tower value t *)
IsSet(t, d) == ((t DIV d) % 2) = 1

(* d must be the smallest disk on the tower *)
SmallestOnTower(t, d) ==
    IsSet(t, d) /\ \A e \in DiskVals : e < d => ~IsSet(t, e)

(* destination must contain no smaller disk *)
DestinationOk(t, d) ==
    \A e \in DiskVals : e < d => ~IsSet(t, e)

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

Move ==
    \E i \in 1..D:
        \E src, dst \in 1..N:
            /\ src # dst
            /\ IsSet(towers[src], Disk(i))
            /\ SmallestOnTower(towers[src], Disk(i))
            /\ DestinationOk(towers[dst], Disk(i))
            /\ towers' = [j \in 1..N |
                            IF j = src THEN towers[j] - Disk(i)
                            ELSE IF j = dst THEN towers[j] + Disk(i)
                            ELSE towers[j]]

Next == Move

Spec == Init /\ [][Next]_towers

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] >= 0 /\ towers[i] < 2 ^ D

Inv ==
    (\Sum i \in 1..N: towers[i]) = 2 ^ D - 1
====