---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES want, inCS, number, ticket, nextTicket

vars == <<want, inCS, number, ticket, nextTicket>>

TypeOK ==
    /\ want \subseteq (1..N)
    /\ inCS \subseteq (1..N)
    /\ number \in 0..MaxNat
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ want = {}
    /\ inCS = {}
    /\ number = 0
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ p \notin want
    /\ p \notin inCS
    /\ want' = want \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE 0
    /\ UNCHANGED <<inCS, number>>

Enter(p) ==
    /\ p \in want
    /\ p \notin inCS
    /\ \A q \in inCS : ticket[p] < ticket[q]
    /\ inCS' = inCS \cup {p}
    /\ want' = want \ {p}
    /\ number' = (number + 1) % (MaxNat + 1)
    /\ UNCHANGED <<ticket, nextTicket>>

Leave(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ number' = (number + 1) % (MaxNat + 1)
    /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Leave(p)

MutualExclusion == \A p \in inCS : \A q \in inCS : p = q

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars
====