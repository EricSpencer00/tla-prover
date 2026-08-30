---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ want = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

Request(i) ==
    /\ ~want[i]
    /\ ~inCS[i]
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Acquire(i) ==
    /\ want[i]
    /\ ~inCS[i]
    /\ \A j \in 1..N : ~inCS[j]
    /\ \A j \in 1..N : ~want[j]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ want' = [want EXCEPT ![i] = FALSE]

Release(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Acquire(i)
    \/ \E i \in 1..N : Release(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N : inCS[i] => (\A j \in 1..N : j # i => ~inCS[j])

Inv == MutualExclusion

ISpec == Spec

NatOverride == Nat

====