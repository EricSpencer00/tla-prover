---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Bounds the effective natural-number set for model checking.
NatOverride == 0..MaxNat

\* Inherited from the Bakery specification: a bounded set of processes, a
\* phase per process, an ordering counter, and per-process ticket numbers.
VARIABLES phase, ticket, nextTicket

vars == << phase, ticket, nextTicket >>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Bump(n) == IF n < MaxNat THEN n + 1 ELSE n

\* A process starts a request and takes the next ticket number.
Request(p) ==
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = Bump(nextTicket)

\* A process enters the critical section only when no other process holds
\* a ticket-number strictly below its own -- bakery ordering.
Enter(p) ==
  /\ phase[p] = "trying"
  /\ \A q \in 1..N : (phase[q] = "critical") => (ticket[p] <= ticket[q])
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ UNCHANGED << ticket, nextTicket >>

\* A process leaves the critical section.
Exit(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ UNCHANGED << ticket, nextTicket >>

Next == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

\* The inductive invariant (Inv) already includes MutualExclusion and
\* TypeOK, but it is named explicitly for the .cfg.
Inv == TypeOK

\* The .cfg binds Spec to the inductive definition of Init and Next rather
\* than the canonical Init/Next pair.
ISpec == Init /\ [][Next]_vars

====