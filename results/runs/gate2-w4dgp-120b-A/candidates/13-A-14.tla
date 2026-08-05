---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, served, ticket, nextTicket

vars == <<inCS, served, ticket, nextTicket>>

TypeOK ==
    /\ inCS \in SUBSET (1..N)
    /\ served \in SUBSET (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ inCS = {}
    /\ served = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ p \notin served
    /\ p \notin inCS
    /\ ticket[p] = 0
    /\ nextTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<inCS, served>>

Enter(p) ==
    /\ p \notin inCS
    /\ ticket[p] # 0
    /\ \A q \in inCS : ticket[p] < ticket[q]
    /\ inCS' = inCS \cup {p}
    /\ UNCHANGED <<served, ticket, nextTicket>>

Exit(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ served' = served \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED nextTicket

Idle == UNCHANGED vars

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ Idle

MutualExclusion == \A p, q \in inCS : p = q

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

====