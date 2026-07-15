---- MODULE Hanoi ----
EXTENDS Naturals, Sequences

CONSTANTS D, N

VARIABLES towers

Towers == 1 .. N
DiskBits == { 2 ^ k | k \in 0 .. D-1 }
AllDiskBits == 2 ^ D - 1

Init ==
    towers = [t \in Towers |-> IF t = 1 THEN AllDiskBits ELSE 0]

Move ==
    \E src \in Towers, dst \in Towers \ {src}, disk \in DiskBits :
        LET
            srcVal = towers[src]
            dstVal = towers[dst]
        IN
            /\ srcVal % (disk * 2) >= disk
            /\ srcVal % disk = 0
            /\ dstVal % disk = 0
            /\ towers' = [t \in Towers |-> 
                            IF t = src THEN srcVal - disk
                            ELSE IF t = dst THEN dstVal + disk
                            ELSE towers[t]]

Next == Move

Spec == Init /\ [][Next]_towers

TypeOK ==
    towers \in [Towers -> Nat] /\ \A t \in Towers : towers[t] < 2 ^ D

Inv == SUM towers = 2 ^ D - 1

====