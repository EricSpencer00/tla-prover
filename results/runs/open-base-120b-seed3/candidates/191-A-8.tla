---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
   Helper definitions
-----------------------------------------------------------------*)
AllDisks == { 2^k : k \in 0..D-1 }

DiskOn(t, d) == ((t \div d) % 2) = 1

IsSmallest(t, d) ==
    DiskOn(t, d) /\ \A d2 \in AllDisks : (d2 < d) => ~DiskOn(t, d2)

NoSmaller(t, d) ==
    \A d2 \in AllDisks : (d2 < d) => ~DiskOn(t, d2)

(*-----------------------------------------------------------------
   State constraints
-----------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] >= 0 /\ towers[i] < 2^D

Inv ==
    /\ \Sum i \in 1..N : towers[i] = 2^D - 1

(*-----------------------------------------------------------------
   Initial state
-----------------------------------------------------------------*)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
    /\ TypeOK

(*-----------------------------------------------------------------
   Next-state relation (one legal move)
-----------------------------------------------------------------*)
Move ==
    \E i, j \in 1..N :
        /\ i # j
        /\ \E d \in AllDisks :
            /\ IsSmallest(towers[i], d)
            /\ NoSmaller(towers[j], d)
            /\ towers' = [towers EXCEPT ![i] = towers[i] - d,
                                         ![j] = towers[j] + d]

Next == Move

(*-----------------------------------------------------------------
   Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

====