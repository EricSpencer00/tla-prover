---- MODULE Hanoi ----
EXTENDS Naturals, Sequences

CONSTANTS D, N

VARIABLES towers

\*--- Helper definitions -------------------------------------------------------

DiskVals == { 2^i : i \in 0..D-1 }

IsPresent(t, d) == (t % (2 * d) >= d)

SmallestOn(t, d) == IsPresent(t, d) /\ (t % d = 0)

NoSmallerOn(t, d) == (t % d = 0)

\*--- Initialization ----------------------------------------------------------

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
    /\ TypeOK
    /\ Inv

\*--- Next-state relation -----------------------------------------------------

Move(i, j, d) ==
    /\ i \in 1..N
    /\ j \in 1..N
    /\ i # j
    /\ d \in DiskVals
    /\ IsPresent(towers[i], d)
    /\ SmallestOn(towers[i], d)
    /\ NoSmallerOn(towers[j], d)
    /\ towers' = [towers EXCEPT ![i] = towers[i] - d,
                                   ![j] = towers[j] + d]

Next ==
    \E i, j \in 1..N: \E d \in DiskVals: Move(i, j, d)

\*--- Specification -----------------------------------------------------------

Spec == Init /\ [][Next]_towers

\*--- Invariants --------------------------------------------------------------

TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2^D

Inv ==
    (+/ << towers[i] : i \in 1..N >>) = 2^D - 1

\*--- The required identifiers ------------------------------------------------

SPECIFICATION Spec
INVARIANTS TypeOK, Inv

====