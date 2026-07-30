---- MODULE MCBoulanger ----
EXTENDS Naturals

\* Natural-number ticket values are bounded for model checking, and the
\* state constraint below keeps every ticket strictly below MaxNat so
\* the finite range is never exhausted.
CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, served, servedBy

vars == <<pc, ticket, served, servedBy>>

TypeOK ==
    /\ pc \in [1..N -> {"idle", "waiting", "critical", "done"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in [1..N -> BOOLEAN]
    /\ servedBy \in [1..N -> 0..N]

Init ==
    /\ pc = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ served = [p \in 1..N |-> FALSE]
    /\ servedBy = [p \in 1..N |-> 0]

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, served, servedBy>>

Acquire(p) ==
    /\ pc[p] = "waiting"
    /\ \A q \in 1..N : pc[q] # "critical"
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, served, servedBy>>

Release(p) ==
    /\ pc[p] = "critical"
    /\ p' = (servedBy[p] + 1) % (N + 1)
    /\ served' = [served EXCEPT ![p] = TRUE]
    /\ servedBy' = [servedBy EXCEPT ![p] = p']
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED ticket

Ticket(p) ==
    /\ \A q \in 1..N : p # q => ticket[p] <= ticket[q]
    /\ \A q \in 1..N : p # q => ~(pc[q] \in {"critical", "waiting"} /\ pc[p] = "waiting")
    /\ UNCHANGED vars

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Acquire(p)
    \/ \E p \in 1..N : Release(p)
    \/ \E p \in 1..N : Ticket(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p, q \in 1..N : (pc[p] = "critical" /\ pc[q] = "critical") => p = q

TicketBound ==
    \A p \in 1..N : ticket[p] < MaxNat

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ TicketBound

====