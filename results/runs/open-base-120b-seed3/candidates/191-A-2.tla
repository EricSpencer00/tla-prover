---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

\* --- Helper definitions -------------------------------------------------
DiskSet == { 2^i : i \in 0..D-1 }

DiskPresent(t, d) == (t % (2 * d) >= d)

SmallestOn(t, d) == DiskPresent(t, d) /\ (t % d = 0)

NoSmaller(t, d) == (t % d = 0)

\* --- Initial state ------------------------------------------------------
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\* --- Move action ---------------------------------------------------------
Move ==
    \E src \in 1..N, dst \in 1..N, d \in DiskSet :
        /\ src # dst
        /\ SmallestOn(towers[src], d)
        /\ NoSmaller(towers[dst], d)
        /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

Next == Move \/ UNCHANGED towers

\* --- Specification --------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* --- Invariants -----------------------------------------------------------
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2^D

Inv ==
    \Sum i \in 1..N : towers[i] = 2^D - 1

====