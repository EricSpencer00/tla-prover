---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

\*--- Helper definitions -------------------------------------------------

DiskSet == { 2^k : k \in 0..(D-1) }

DiskPresent(t, d) == (t % (2 * d)) >= d

SmallestOn(t, d) ==
    DiskPresent(t, d) /\ 
    \A e \in DiskSet : (e < d) => ~DiskPresent(t, e)

DestOk(t, d) ==
    \A e \in DiskSet : (e < d) => ~DiskPresent(t, e)

\*--- Initialization -----------------------------------------------------

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

\*--- Move action --------------------------------------------------------

Move(d, s, t) ==
    /\ s # t
    /\ DiskPresent(towers[s], d)
    /\ SmallestOn(towers[s], d)
    /\ DestOk(towers[t], d)
    /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                               ![t] = towers[t] + d]

Next ==
    \E d \in DiskSet :
        \E s \in 1..N :
            \E t \in 1..N :
                Move(d, s, t)

\*--- Specification -------------------------------------------------------

Spec ==
    Init /\ [][Next]_towers

\*--- Invariants ---------------------------------------------------------

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2^D

Inv ==
    Sum({towers[i] : i \in 1..N}) = 2^D - 1

====