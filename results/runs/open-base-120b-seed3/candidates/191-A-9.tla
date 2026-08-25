---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

(*--- Helper definitions -----------------------------------*)

Disk(i) == 2 ^ i

DiskSet == { Disk(i) : i \in 0..(D-1) }

MaxValue == 2 ^ D - 1

(*--- State variable ---------------------------------------*)

VARIABLES towers

(*--- Predicate definitions --------------------------------*)

IsOn(t, d) == ((t DIV d) % 2 = 1)

NoSmaller(t, d) == (t % d = 0)

(*--- Initialization ---------------------------------------*)

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN MaxValue ELSE 0]

(*--- Move action ------------------------------------------*)

Move ==
    \E d \in DiskSet :
        \E src \in 1..N :
            \E dst \in 1..N :
                /\ src # dst
                /\ IsOn(towers[src], d)
                /\ NoSmaller(towers[src], d)
                /\ NoSmaller(towers[dst], d)
                /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                           ![dst] = towers[dst] + d]

(*--- Next-state relation ----------------------------------*)

Next ==
    \/ Move
    \/ UNCHANGED towers

(*--- Specification ----------------------------------------*)

Spec == Init /\ [][Next]_towers

(*--- Invariants -------------------------------------------*)

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv ==
    /\ \Sum i \in 1..N : towers[i] = MaxValue

====