---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS
    N, MaxNat

VARIABLES
    wants, tickets, inCS, ticketCount

Nat == 0..MaxNat

TypeOK ==
    /\ wants \in [0..N-1 -> BOOLEAN]
    /\ tickets \in [0..N-1 -> Nat]
    /\ inCS \in [0..N-1 -> BOOLEAN]
    /\ ticketCount \in Nat

Init ==
    /\ wants = [p \in 0..N-1 |-> FALSE]
    /\ tickets = [p \in 0..N-1 |-> 0]
    /\ inCS = [p \in 0..N-1 |-> FALSE]
    /\ ticketCount = 0

\* Bakery entry: take a ticket strictly greater than every outstanding ticket.
Request(p) ==
    /\ wants[p] = FALSE
    /\ wants' = [wants EXCEPT ![p] = TRUE]
    /\ tickets' = [tickets EXCEPT ![p] = ticketCount]
    /\ ticketCount' = IF ticketCount < MaxNat THEN ticketCount + 1 ELSE ticketCount
    /\ UNCHANGED inCS

\* Enter the critical section when no one with a strictly lower ticket is waiting.
Enter(p) ==
    /\ wants[p] = TRUE
    /\ \A q \in 0..N-1 : ~(wants[q] = TRUE /\ tickets[q] < tickets[p])
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<wants, tickets, ticketCount>>

\* Exit the critical section and clear the request.
Exit(p) ==
    /\ inCS[p] = TRUE
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ wants' = [wants EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<tickets, ticketCount>>

Next ==
    \/ \E p \in 0..N-1 : Request(p)
    \/ \E p \in 0..N-1 : Enter(p)
    \/ \E p \in 0..N-1 : Exit(p)

ISpec == Init /\ [][Next]_<<wants, tickets, inCS, ticketCount>>

MutualExclusion ==
    \A p \in 0..N-1 : inCS[p] => (wants[p] /\ \A q \in 0..N-1 : (q # p /\ inCS[q]) => tickets[q] > tickets[p])

Inv ==
    /\ MutualExclusion
    /\ TypeOK

====