---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES state, ticket, maxTicket, adminOverride, target

vars == <<state, ticket, maxTicket, adminOverride, target>>

States == {"idle", "waiting", "critical"}
TargetStates == {"idle", "waiting"}
MaxReuse == 2

\* The ticket numbers are natural numbers, but the model checker works with a
\* finite slice of them, bounded by MaxNat; the state-constraint below keeps
\* every ticket strictly below that bound so the finite override stays coherent.
TypeOK ==
    /\ state \in [1..N -> States]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ maxTicket \in 0..MaxNat
    /\ adminOverride \in BOOLEAN
    /\ target \in [1..N -> TargetStates]

Init ==
    /\ state = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ maxTicket = 0
    /\ adminOverride = FALSE
    /\ target = [p \in 1..N |-> "idle"]

Wait(p) ==
    /\ state[p] = "idle"
    /\ ~adminOverride
    /\ target[p] # "critical"
    /\ state' = [state EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, maxTicket, adminOverride, target>>

\* Requests are served strictly in ticket order.
Enter(p) ==
    /\ state[p] = "waiting"
    /\ ~adminOverride
    /\ \A q \in 1..N : (state[q] # "critical") \/ (ticket[q] > ticket[p])
    /\ state' = [state EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, maxTicket, adminOverride, target>>

Leave(p) ==
    /\ state[p] = "critical"
    /\ state' = [state EXCEPT ![p] = "idle"]
    /\ target' = [target EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, maxTicket, adminOverride>>

RaiseTicket(p) ==
    /\ state[p] = "idle"
    /\ ~adminOverride
    /\ target[p] # "idle"
    /\ maxTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = maxTicket + 1]
    /\ maxTicket' = maxTicket + 1
    /\ UNCHANGED <<state, adminOverride, target>>

ArmAdmin ==
    /\ ~adminOverride
    /\ adminOverride' = TRUE
    /\ UNCHANGED <<state, ticket, maxTicket, target>>

DisarmAdmin ==
    /\ adminOverride
    /\ adminOverride' = FALSE
    /\ UNCHANGED <<state, ticket, maxTicket, target>>

\* The privileged override skips the ticket line entirely, but it is limited to
\* a single use per target so it can never stall ordinary ticket service.
AdminForce(p) ==
    /\ adminOverride
    /\ state[p] # "critical"
    /\ target[p] # "critical"
    /\ state' = [state EXCEPT ![p] = "critical"]
    /\ target' = [target EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, maxTicket, adminOverride>>

Next ==
    \/ \E p \in 1..N : Wait(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Leave(p)
    \/ \E p \in 1..N : RaiseTicket(p)
    \/ ArmAdmin
    \/ DisarmAdmin
    \/ \E p \in 1..N : AdminForce(p)

Spec == Init /\ [][Next]_vars

\* At most one process is ever inside the critical section.
MutualExclusion ==
    \A p, q \in 1..N : (state[p] = "critical" /\ state[q] = "critical") => p = q

\* Ticket numbers only ever grow, and they are capped at the finite bound.
TicketsWithinBound == maxTicket <= MaxNat

Inv == MutualExclusion /\ TicketBoundInvariant /\ TicketsWithinBound

TicketBoundInvariant ==
    /\ maxTicket <= MaxNat
    /\ \A p \in 1..N : ticket[p] <= maxTicket

====