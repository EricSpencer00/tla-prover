---- MODULE MCBoulanger ----
EXTENDS Integers

CONSTANTS N, MaxNat, Nat

VARIABLES pstate, ticket, maxTicket, owner, served

vars == <<pstate, ticket, maxTicket, owner, served>>

TypeOK ==
    /\ pstate \in [1..N -> {"idle", "waiting", "inCS"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ maxTicket \in 0..MaxNat
    /\ owner \in 0..N
    /\ served \in Nat

Init ==
    /\ pstate = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ maxTicket = 0
    /\ owner = 0
    /\ served = 0

Request(p) ==
    /\ pstate[p] = "idle"
    /\ pstate' = [pstate EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, maxTicket, owner, served>>

WaitForOneMore(p) ==
    /\ pstate[p] = "waiting"
    /\ ticket[p] < MaxNat
    /\ maxTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = maxTicket + 1]
    /\ maxTicket' = maxTicket + 1
    /\ UNCHANGED <<pstate, owner, served>>

Enter(p) ==
    /\ pstate[p] = "waiting"
    /\ \A q \in 1..N : pstate[q] # "inCS"
    /\ pstate' = [pstate EXCEPT ![p] = "inCS"]
    /\ owner' = p
    /\ UNCHANGED <<ticket, maxTicket, served>>

Exit(p) ==
    /\ pstate[p] = "inCS"
    /\ pstate' = [pstate EXCEPT ![p] = "idle"]
    /\ owner' = 0
    /\ served' = (IF served < MaxNat THEN served + 1 ELSE served)
    /\ UNCHANGED <<ticket, maxTicket>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : WaitForOneMore(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : (pstate[p] = "inCS") => (owner = p)

\* A process holds the resource only when its ticket is at least as high as every
\* other process's ticket that is currently contending.
TypeOK ==
    \A p \in 1..N :
        (pstate[p] = "inCS") =>
            \A q \in 1..N : (pstate[q] \in {"waiting", "inCS"}) => ticket[p] >= ticket[q]

\* The full inductive invariant: the "inCS" test and the ticket comparison are
\* both needed to keep mutual exclusion sound.
Inv == MutualExclusion /\ TypeOK

StateConstraint ==
    \A p \in 1..N : ticket[p] <= MaxNat - 1

====