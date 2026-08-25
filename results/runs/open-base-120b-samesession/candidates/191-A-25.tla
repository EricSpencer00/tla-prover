---- MODULE Hanoi ----
EXTENDS Naturals, TLC, Bitwise

CONSTANTS D, N

VARIABLES towers

(* Helper definitions *)
Disk(i) == 2 ^ i
AllDisks == 2 ^ D - 1
DiskSet == { d \in Nat : \E i \in 0..(D-1) : d = Disk(i) }

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

IsSmallest(t, d) == (t Mod d = 0) /\ (And(t, d) = d)

CanPlace(t, d) == (t Mod d = 0)

Move ==
    \E d \in DiskSet:
        \E src, dst \in 1..N:
            /\ src # dst
            /\ And(towers[src], d) = d
            /\ IsSmallest(towers[src], d)
            /\ CanPlace(towers[dst], d)
            /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

Next == Move

Spec == Init /\ [][Next]_towers

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2 ^ D

Inv ==
    \Sum i \in 1..N: towers[i] = AllDisks

====