---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The ticket numbers are only explored up to MaxNat-1, and the finite
\* override of Naturals is kept by the state constraint below.
VARIABLES pc, csOwner, ticket, maxTicket

vars == << pc, csOwner, ticket, maxTicket >>

Idle == "idle"
Waiting == "waiting"
Served == "served"

TypeOK ==
  /\ pc \in [1..N -> {Idle, Waiting, Served}]
  /\ csOwner \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat

\* A state constraint: ticket numbers never hit the finite ceiling.
BoundedTickets == \A i \in 1..N : ticket[i] < MaxNat

\* Mutual exclusion: when the critical section is held exactly one process
\* holds it, and whoever holds it is in the critical section.
MutualExclusion ==
  /\ (csOwner = 0) <=> (\A i \in 1..N : pc[i] # Served)
  /\ \A i \in 1..N : (pc[i] = Served) => (csOwner = i)

\* The full inductive invariant the Boulanger algorithm carries.
Inv == MutualExclusion /\ TypeOK

Init ==
  /\ pc = [i \in 1..N |-> Idle]
  /\ csOwner = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ maxTicket = 0

Enter(i) ==
  /\ pc[i] = Idle
  /\ csOwner = 0
  /\ pc' = [pc EXCEPT ![i] = Waiting]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ UNCHANGED csOwner

EnterCS(i) ==
  /\ pc[i] = Waiting
  /\ csOwner = 0
  /\ \A j \in 1..N : ticket[j] <= ticket[i]
  /\ csOwner' = i
  /\ pc' = [pc EXCEPT ![i] = Served]
  /\ UNCHANGED << ticket, maxTicket >>

Exit(i) ==
  /\ pc[i] = Served
  /\ csOwner = i
  /\ csOwner' = 0
  /\ pc' = [pc EXCEPT ![i] = Idle]
  /\ UNCHANGED << ticket, maxTicket >>

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : EnterCS(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

\* Liveness properties are not specified for this configuration module.
====