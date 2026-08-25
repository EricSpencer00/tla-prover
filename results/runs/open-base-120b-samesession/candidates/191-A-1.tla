---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Disk values are powers of two: 1, 2, 4, ..., 2^(D-1) *)
DiskVals == { 2^(i-1) : i \in 1..D }

Init ==
    towers = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]

Move ==
    \E src, dst \in 1..N :
        \E d \in DiskVals :
            /\ src # dst
            /\ LET srcVal == towers[src], dstVal == towers[dst] IN
                 /\ ((srcVal \div d) % 2) = 1           \* disk d is present on src
                 /\ srcVal % d = 0                     \* d is the smallest disk on src
                 /\ dstVal % d = 0                     \* no smaller disk on dst
                 /\ towers' = [t \in 1..N |-> 
                        IF t = src THEN srcVal - d
                        ELSE IF t = dst THEN dstVal + d
                        ELSE towers[t]]

Next == Move

Spec == Init /\ [][Next]_towers

TypeOK ==
    \A t \in 1..N : towers[t] \in Nat /\ towers[t] < 2^D

Inv ==
    Sum(t \in 1..N, towers[t]) = 2^D - 1

====