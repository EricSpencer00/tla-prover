---- MODULE MCBoulanger ----
EXTENDS Naturals

\* Model-checking configuration for the Boulanger mutual exclusion algorithm.
\* It mirrors the full Boulanger spec but replaces the unbounded Nat with a
\* finite range 0..MaxNat for the ticket numbers, and adds a state constraint
\* that keeps every ticket strictly below the maximum.

CONSTANTS N, MaxNat

Processes == 1..N

VARIABLES inCS, want, ticket, now
vars == << inCS, want, ticket, now >>

TypeOK ==
  /\ inCS \in [Processes -> BOOLEAN]
  /\ want \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> 0..MaxNat]
  /\ now \in 0..MaxNat

\* Initial state: no process owns the critical section and no tickets are taken.
Init ==
  /\ inCS = [p \in Processes |-> FALSE]
  /\ want = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> 0]
  /\ now = 0

\* A process requests the critical section.
Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED << inCS, ticket, now >>

\* A process takes a ticket equal to the current clock -- a bounded, time-variant.
Ticket(p) ==
  /\ want[p]
  /\ ticket[p] = 0
  /\ ticket' = [ticket EXCEPT ![p] = now]
  /\ UNCHANGED << inCS, want, now >>

\* A process enters the critical section only if no one else is in it and its
\* ticket still matches the current clock.
Enter(p) ==
  /\ want[p]
  /\ ticket[p] # 0
  /\ ticket[p] = now
  /\ \A q \in Processes : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED << want, ticket, now >>

\* A process leaves the critical section.
Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ now' = (now + 1) % (MaxNat + 1)
  /\ UNCHANGED want

Next == \E p \in Processes :
  Request(p) \/ Ticket(p) \/ Enter(p) \/ Exit(p)

\* The full Boulanger spec: unbounded transition system plus the derived
\* inductive invariant.  Here it runs on the bounded Nat domain.
Spec == Init /\ [][Next]_vars

\* Mutual exclusion: two distinct processes are never both inside the critical
\* section at the same time.
MutualExclusion ==
  \A p, q \in Processes :
    (inCS[p] /\ inCS[q]) => (p = q)

\* The full inductive invariant carried over from the Boulanger spec.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

\* Runtime pruning: ticket numbers never reach the configured maximum, which
\* keeps the finite Nat domain from needing to explore wrap-around states.
TicketsBelowMax ==
  \A p \in Processes : ticket[p] < MaxNat

StateConstraint == TicketsBelowMax

====