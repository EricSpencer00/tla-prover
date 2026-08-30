---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket, served

vars == <<inCS, want, ticket, nextTicket, served>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ served \in 0..MaxNat

Init ==
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ want = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ served = 0

Request(p) ==
    /\ ~want[p]
    /\ ~inCS[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket, served>>

Enter(p) ==
    /\ want[p]
    /\ \A q \in 1..N : ~inCS[q]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED served

Exit(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : inCS[p] => (\A q \in 1..N : q # p => ~inCS[q])

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A p \in 1..N : inCS[p] => (ticket[p] < nextTicket)

TicketBound == \A p \in 1..N : ticket[p] < MaxNat

====