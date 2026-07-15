---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES Towers

DiskSet == {2^k | k \in 0 .. D-1}

Init ==
    Towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

Next ==
    \E s \in 1..N, d \in 1..N \ {s}, disk \in DiskSet :
        /\ (Towers[s] \# disk) = disk
        /\ (Towers[s] \# (disk - 1)) = 0
        /\ (Towers[d] \# (disk - 1)) = 0
        /\ Towers' = [i \in 1..N |-> IF i = s THEN Towers[i] - disk
                                      ELSE IF i = d THEN Towers[i] + disk
                                      ELSE Towers[i]]
    \/ UNCHANGED Towers

Spec == Init /\ [][Next]_Towers

TypeOK ==
    \A i \in 1..N : Towers[i] \in 0 .. (2^D - 1)

Inv ==
    Sum(Towers) = 2^D - 1

====