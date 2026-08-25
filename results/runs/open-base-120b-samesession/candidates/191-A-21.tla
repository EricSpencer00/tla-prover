---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANT D, N

VARIABLES towers

\* --- Helper definitions -------------------------------------------------

DiskSet == { 2 ^ i : i \in 0..D-1 }

Disk(i) == 2 ^ i

IsDisk(d) == d \in DiskSet

\* d is the smallest disk present on tower value t
SmallestOn(t, d) ==
    /\ IsDisk(d)
    /\ (t % (2 * d) = d)

\* No disk smaller than d is present on tower value t
NoSmaller(t, d) ==
    (t % (2 * d) = 0)

\* --- Initial state -------------------------------------------------------

Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

\* --- Type correctness invariant -----------------------------------------

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2 ^ D

\* --- Conservation invariant ---------------------------------------------

Inv ==
    Sum({ towers[i] : i \in 1..N }) = 2 ^ D - 1

\* --- Move action ---------------------------------------------------------

Move ==
    \E i \in 0..D-1 :
        \E src \in 1..N :
            \E dst \in 1..N :
                /\ src # dst
                LET d == 2 ^ i IN
                    /\ SmallestOn(towers[src], d)
                    /\ NoSmaller(towers[dst], d)
                    /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                             ![dst] = towers[dst] + d]

Next == Move

\* --- Specification -------------------------------------------------------

Spec == Init /\ [][Next]_<<towers>>

====