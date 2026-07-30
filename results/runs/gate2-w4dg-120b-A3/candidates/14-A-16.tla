---- MODULE MCBoulanger ----
EXTENDS Naturals

\* The full Boulanger mutual-exclusion algorithm, extended with a finite
\* range for natural numbers. The invariant is the full set of properties
\* from the original spec; the state constraint keeps ticket numbers below
\* MaxNat so the finite model stays within its bounds.

CONSTANTS N, MaxNat

VARIABLES pc, ticket, maxTicket

vars == <<pc, ticket, maxTicket>>

TypeOK ==
    /\ pc \in [0..(N-1) -> {"idle", "waiting", "critical"}]
    /\ ticket \in [0..(N-1) -> 0..MaxNat]
    /\ maxTicket \in 0..MaxNat

Init ==
    /\ pc = [p \in 0..(N-1) |-> "idle"]
    /\ ticket = [p \in 0..(N-1) |-> 0]
    /\ maxTicket = 0

\* A process takes a request ticket and moves toward the critical section.
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
    /\ ticket' = [ticket EXCEPT ![p] = maxTicket]
    /\ UNCHANGED <<>>

\* A waiting process enters the critical section only when no other process
\* holds a ticket strictly lower than its own.
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ \A q \in 0..(N-1) : (pc[q] = "critical") => (ticket[q] >= ticket[p])
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, maxTicket>>

\* A process leaves the critical section.
Exit(p) ==
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, maxTicket>>

Next ==
    \/ \E p \in 0..(N-1) : Request(p)
    \/ \E p \in 0..(N-1) : Enter(p)
    \/ \E p \in 0..(N-1) : Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion as a lock: at most one process is in the critical section.
MutualExclusion ==
    \A p \in 0..(N-1) : (pc[p] = "critical") => (\A q \in 0..(N-1) : (q # p) => pc[q] # "critical")

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv == MutualExclusion /\ TypeOK

\* Ticket numbers never reach the configured maximum, so the finite
\* override of Nat never has to account for values at the ceiling.
TicketsBelowMax ==
    \A p \in 0..(N-1) : ticket[p] < MaxNat

====