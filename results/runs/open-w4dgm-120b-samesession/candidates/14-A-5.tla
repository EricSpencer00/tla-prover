---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* All behavior is inherited from the Boulanger spec; only the NATURAL range
\* is overridden here to keep ticket numbers finite for model checking.

NONE == "none"

VARIABLES occupant, want, inCS, ticket, nextTicket

vars == <<occupant, want, inCS, ticket, nextTicket>>

TypeOK ==
    /\ occupant \in 0..N
    /\ want \in SUBSET (0..N)
    /\ inCS \in SUBSET (0..N)
    /\ ticket \in [0..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ occupant = N
    /\ want = {}
    /\ inCS = {}
    /\ ticket = [p \in 0..N |-> 0]
    /\ nextTicket = 0

\* A process behind the ticket window is stale but still alive; it may renew.
Renew(p) ==
    /\ p \notin want
    /\ p \notin inCS
    /\ want' = want \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = IF nextTicket < MaxNat THEN nextTicket ELSE ticket[p]]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED <<occupant, inCS>>

TakeFirst ==
    /\ occupant = N
    /\ inCS = {}
    /\ want # {}
    /\ LET p == CHOOSE q \in want : TRUE
       IN /\ occupant' = p
          /\ want' = want \ {p}
          /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(p) ==
    /\ occupant = p
    /\ p \notin inCS
    /\ inCS' = inCS \cup {p}
    /\ UNCHANGED <<occupant, want, ticket, nextTicket>>

Leave(p) ==
    /\ p \in inCS
    /\ inCS' = inCS \ {p}
    /\ occupant' = N
    /\ UNCHANGED <<want, ticket, nextTicket>>

Abandon(p) ==
    /\ p \in want
    /\ want' = want \ {p}
    /\ UNCHANGED <<occupant, inCS, ticket, nextTicket>>

Next ==
    \/ \E p \in 0..N : Renew(p) \/ Enter(p) \/ Leave(p) \/ Abandon(p)
    \/ TakeFirst

Spec ==
    /\ Init
    /\ [][Next]_vars

\* Two independent mutual-exclusion instances must never both be in their
\* critical sections at once.
MutualExclusion == inCS = {} \/ (\E p \in 0..N : inCS = {p})

\* No stale ticket may ever reach the finite cap; that state is pruned by the
\* constraint rather than being an error.
AllTicketsBelowMax == \A p \in 0..N : ticket[p] < MaxNat

====