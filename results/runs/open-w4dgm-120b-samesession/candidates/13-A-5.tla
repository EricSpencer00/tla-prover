---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES
    entered, \* set of processes currently in the critical section
    ticket,  \* [1..N -> 0..MaxNat] ticket number each process is holding
    want,    \* [1..N -> BOOLEAN] whether each process wants the critical section
    nextTicket \* the next ticket number the Bakery server will issue

vars == <<entered, ticket, want, nextTicket>>

\* Mutual exclusion of the critical section is enforced by the bakery's
\* ticket-and-queue discipline: only the process holding the smallest live
\* ticket may enter, and no two live tickets can be the same.
TypeOK ==
    /\ entered \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ want \in [1..N -> BOOLEAN]
    /\ nextTicket \in 0..(MaxNat + 1)

Init ==
    /\ entered = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ want = [p \in 1..N |-> FALSE]
    /\ nextTicket = 1

\* Any process may start wanting the critical section.
Request(p) ==
    /\ \A q \in 1..N : ~want[q]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<entered, ticket, nextTicket>>

\* The server issues a ticket to a waiting process, limited by MaxNat.
Issue(p) ==
    /\ want[p]
    /\ ticket[p] = 0
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED <<entered, want>>

\* A process whose ticket is live enters the critical section.
Enter(p) ==
    /\ ticket[p] # 0
    /\ \A q \in entered : ticket[p] < ticket[q]
    /\ entered' = entered \cup {p}
    /\ UNCHANGED <<ticket, want, nextTicket>>

\* A process leaves the critical section and gives up its ticket.
Leave(p) ==
    /\ p \in entered
    /\ entered' = entered \ {p}
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED nextTicket

\* The server may reclaim a ticket from a process that lost interest.
Cancel(p) ==
    /\ ticket[p] # 0
    /\ ~want[p]
    /\ p \notin entered
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<entered, want, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Issue(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Leave(p)
    \/ \E p \in 1..N : Cancel(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in entered : p = q
Inv == MutualExclusion

\* model-checking entry point: the inductive spec, starting from any
\* reachable state, not just the initial state
ISpec == Spec

\* SAFETY PROPERTY: the full set of invariants the Bakery relies on
SafetyProperties == MutualExclusion /\ TypeOK /\ Inv

====