---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

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

Enter(i) ==
    /\ want[i]
    /\ ~inCS[i]
    /\ nextTicket < MaxNat
    /\ \A j \in 1..N : ~inCS[j]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ want' = [want EXCEPT ![i] = FALSE]

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

Inv ==
    /\ \A i \in 1..N : inCS[i] => (ticket[i] = nextTicket - 1)
    /\ \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====