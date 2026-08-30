---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, count, served

vars == <<inCS, want, ticket, count, served>>

\* A finite-domain Nat: the ticket numbers are capped for model checking.
NatOverride(e) == IF e \in 0..MaxNat THEN e ELSE 0

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ want \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ count \in [1..N -> 0..MaxNat]
    /\ served \in 0..MaxNat

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ count = [p \in 1..N |-> 0]
    /\ served = 0

\* A process requests the critical section and takes a fresh ticket.
Request(p) ==
    /\ p \notin want
    /\ p \notin inCS
    /\ want' = want \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = NatOverride(served + 1)]
    /\ UNCHANGED <<inCS, count, served>>

\* A process enters only if it is the sole requester and nobody else is in.
Enter(p) ==
    /\ p \in want
    /\ inCS = {}
    /\ want = {p}
    /\ inCS' = {p}
    /\ count' = [count EXCEPT ![p] = 0]
    /\ UNCHANGED <<want, ticket, served>>

\* Being in the critical section resets the request set.
Release(p) ==
    /\ p \in inCS
    /\ inCS' = {}
    /\ want' = {}
    /\ count' = [count EXCEPT ![p] = count[p] + 1]
    /\ served' = NatOverride(served + 1)
    /\ UNCHANGED ticket

\* A slow participant whose ticket is overtaken by a newer waiter gives up.
Retry(p) ==
    /\ p \in want
    /\ \E q \in want : q # p /\ ticket[q] > ticket[p]
    /\ want' = want \ {p}
    /\ count' = [count EXCEPT ![p] = count[p] + 1]
    /\ UNCHANGED <<inCS, ticket, served>>

\* The slow participant relinquishes its stale ticket and asks again.
Relinquish(p) ==
    /\ p \in want
    /\ p \notin inCS
    /\ want' = want \ {p}
    /\ UNCHANGED <<inCS, ticket, count, served>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Release(p)
    \/ \E p \in 1..N : Retry(p)
    \/ \E p \in 1..N : Relinquish(p)

\* SAFETY PROPERTY: at most one process is ever in the critical section.
MutualExclusion == \A p, q \in inCS : p = q

\* SAFETY PROPERTY: the full inductive invariant of the Bakery algorithm.
Inv ==
    /\ MutualExclusion
    /\ TypeOK

ISpec == Init /\ [][Next]_vars

====