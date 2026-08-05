---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES entering, tickets, inCS, nextTicket
vars == <<entering, tickets, inCS, nextTicket>>

\* The Bakery spec's ticket numbering is now on a finite range 0..MaxNat instead of Nat
NatOverride == 0..MaxNat

TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ tickets \in [1..N -> NatOverride]
    /\ inCS \subseteq (1..N)
    /\ nextTicket \in NatOverride

Init ==
    /\ entering = [i \in 1..N |-> FALSE]
    /\ tickets = [i \in 1..N |-> 0]
    /\ inCS = {}
    /\ nextTicket = 0

Request(i) ==
    /\ ~entering[i]
    /\ tickets' = [tickets EXCEPT ![i] = nextTicket]
    /\ entering' = [entering EXCEPT ![i] = TRUE]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)
    /\ UNCHANGED inCS

Enter(i) ==
    /\ entering[i]
    /\ \A j \in 1..N : (entering[j] => tickets[i] <= tickets[j])
    /\ inCS' = inCS \cup {i}
    /\ entering' = [entering EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<tickets, nextTicket>>

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ UNCHANGED <<entering, tickets, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

MutualExclusion == \A a, b \in inCS : a = b
Inv ==
    /\ TypeOK
    /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

====