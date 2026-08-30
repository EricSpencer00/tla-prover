---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES entering, inCS, ticket, nextTicket, waiting

vars == <<entering, inCS, ticket, nextTicket, waiting>>

\* The ticket numbers are capped by MaxNat, which is what keeps the reachable
\* state space finite for model checking.
\* CappedTicket is the ticket a process would take, saturating at MaxNat.
CappedTicket(t) == IF t < MaxNat THEN t + 1 ELSE t

TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ waiting \in [1..N -> BOOLEAN]

Init ==
    /\ entering = [p \in 1..N |-> FALSE]
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ waiting = [p \in 1..N |-> FALSE]

Request(p) ==
    /\ ~waiting[p]
    /\ ~entering[p]
    /\ ~inCS[p]
    /\ waiting' = [waiting EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<entering, inCS, ticket, nextTicket>>

\* Takes a ticket, saturating at the configured maximum rather than growing
\* without bound.
TakeTicket(p) ==
    /\ waiting[p]
    /\ ticket[p] = 0
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = CappedTicket(nextTicket)
    /\ UNCHANGED <<entering, inCS, waiting>>

\* A process may enter only if its own ticket is strictly smaller than every
\* other process's ticket that is currently valid (non-zero) -- this is the
\* bakery's rank check that rules out a stale winner overtaking a newer one.
Enter(p) ==
    /\ waiting[p]
    /\ ticket[p] # 0
    /\ \A q \in 1..N : (q # p /\ ticket[q] # 0) => ticket[p] < ticket[q]
    /\ entering' = [entering EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket, waiting>>

GoToCS(p) ==
    /\ entering[p]
    /\ entering' = [entering EXCEPT ![p] = FALSE]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, nextTicket, waiting>>

Leave(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ waiting' = [waiting EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<entering, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : TakeTicket(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : GoToCS(p)
    \/ \E p \in 1..N : Leave(p)

Spec == Init /\ [][Next]_vars

\* The only mutually exclusive resource is the critical section: two
\* processes may never both be inside it at the same time.
MutualExclusion ==
    \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

\* Every process that is in the critical section is the sole current holder
\* and had a real (non-stale) ticket; this is another way of ruling out a
\* process acting on a stale, second-from-the-front ticket.
Inv ==
    \A p \in 1..N :
        inCS[p] =>
            /\ \A q \in 1..N : ~inCS[q] \/ q = p
            /\ ticket[p] # 0

ISpec == Spec

NatOverride == Nat

====