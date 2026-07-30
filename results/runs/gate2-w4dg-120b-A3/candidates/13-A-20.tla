---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, next, served, servedBound

vars == <<inCS, ticket, next, served, servedBound>>

Processing == { i \in 1..N : ticket[i] > 0 }

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ next \in 0..MaxNat
    /\ served \in 0..MaxNat
    /\ servedBound \in 0..MaxNat

Init ==
    /\ inCS = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ next = 0
    /\ served = 0
    /\ servedBound = 0

TakeTicket(i) ==
    /\ i \notin inCS
    /\ ticket[i] = 0
    /\ next < MaxNat
    /\ ticket' = [ticket EXCEPT ![i] = next + 1]
    /\ next' = next + 1
    /\ UNCHANGED <<inCS, served, servedBound>>

Enter(i) ==
    /\ ticket[i] > 0
    /\ i \notin inCS
    /\ \A j \in Processing : ticket[j] > ticket[i]
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED <<ticket, next, served, servedBound>>

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ UNCHANGED <<next, servedBound>>

ServedBound(i) ==
    /\ ticket[i] > 0
    /\ ticket[i] <= servedBound
    /\ servedBound' = IF servedBound < MaxNat THEN servedBound + 1 ELSE servedBound
    /\ UNCHANGED <<inCS, ticket, next, served>>

Next ==
    \/ \E i \in 1..N : TakeTicket(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ \E i \in 1..N : ServedBound(i)

Inv ==
    /\ MutualExclusion
    /\ TypeOK

MutualExclusion ==
    \A a, b \in inCS : a = b

ISpec == Init /\ [][Next]_vars

====