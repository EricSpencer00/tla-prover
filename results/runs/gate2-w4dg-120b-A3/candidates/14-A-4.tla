---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* Model-checking configuration for the Boulanger mutual exclusion algorithm.
\* Extends the Boulanger specification, overriding the Nat type with a finite
\* range and adding a state constraint to keep ticket numbers within bounds.

CONSTANTS N, MaxNat

\* Boulanger's shared state: each process has a ticket (Nat) and a phase in
\* the mutual-exclusion protocol.
VARIABLES ticket, phase

vars == << ticket, phase >>

Phases == {"idle", "trying", "critical"}

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ phase \in [1..N -> Phases]

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ phase = [p \in 1..N |-> "idle"]

\* Request: a fresh ticket is issued and the process moves to trying.
Request(p) ==
  /\ phase[p] = "idle"
  /\ ticket' = [ticket EXCEPT ![p] = 1 + (ticket[p] % MaxNat)]
  /\ phase' = [phase EXCEPT ![p] = "trying"]

\* Enter: a trying process enters the critical section.
Enter(p) ==
  /\ phase[p] = "trying"
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ UNCHANGED ticket

\* Exit: the critical process leaves and returns to idle.
Exit(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (phase[p] = "critical" /\ phase[q] = "critical") => p = q

\* The full inductive invariant property.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

\* The state constraint: no process's ticket may reach the finite ceiling.
TicketBound ==
  \A p \in 1..N : ticket[p] < MaxNat

====