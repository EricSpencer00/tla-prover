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
    /\ \A j \in 1..N : ~inCS[j]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED want

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i \in 1..N : inCS[i] => (\A j \in 1..N : j # i => ~inCS[j])

Inv ==
    /\ MutualExclusion
    /\ TypeOK

TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====