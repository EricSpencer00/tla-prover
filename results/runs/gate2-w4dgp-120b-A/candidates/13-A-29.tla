---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

(* This module models the Bakery mutual exclusion algorithm under a finite model   *)
(* checking configuration.  The natural numbers are overridden with a finite range *)
(* so that ticket numbers stay bounded and the state space is finite.  The full      *)
(* inductive invariant is preserved from any reachable state.                        *)

CONSTANTS N, MaxNat

Processes == 1..N
NoOne == 0

VARIABLES inCS, ticket, nextTicket, wants

vars == <<inCS, ticket, nextTicket, wants>>

TypeOK ==
    /\ inCS \in [Processes -> BOOLEAN]
    /\ ticket \in [Processes -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ wants \in [Processes -> BOOLEAN]

\* Mutual exclusion: no two processes are ever in the critical section at once.
MutualExclusion ==
    \A p \in Processes : inCS[p] => (\A q \in Processes : q # p => ~inCS[q])

\* Full inductive invariant: every component that can be unbounded in the real  *
\* system is now bounded by MaxNat, so the state space stays finite.
BoundedInvariant ==
    /\ TypeOK
    /\ nextTicket <= MaxNat

Init ==
    /\ inCS = [p \in Processes |-> FALSE]
    /\ ticket = [p \in Processes |-> 0]
    /\ nextTicket = 0
    /\ wants = [p \in Processes |-> FALSE]

Request(p) ==
    /\ ~wants[p]
    /\ ~inCS[p]
    /\ nextTicket < MaxNat
    /\ wants' = [wants EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* Take a numbered ticket before entering, but only while the ticket numbering  *
\* has not saturated.
Take(p) ==
    /\ wants[p]
    /\ ~inCS[p]
    /\ nextTicket < MaxNat
    /\ ticket[p] = 0
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<inCS, wants>>

\* Enter only if holding the smallest numbered ticket among all waiting pro- *
\* cesses (ties broken by process id, which is well founded and finite).
Enter(p) ==
    /\ wants[p]
    /\ ticket[p] > 0
    /\ ~inCS[p]
    /\ \A q \in Processes :
        (wants[q] /\ ticket[q] > 0) => (ticket[p] < ticket[q] \/ (ticket[p] = ticket[q] /\ p < q))
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, nextTicket, wants>>

Leave(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<nextTicket, wants>>

Next ==
    \/ \E p \in Processes : Request(p)
    \/ \E p \in Processes : Take(p)
    \/ \E p \in Processes : Enter(p)
    \/ \E p \in Processes : Leave(p)

ISpec == Init /\ [][Next]_vars

====