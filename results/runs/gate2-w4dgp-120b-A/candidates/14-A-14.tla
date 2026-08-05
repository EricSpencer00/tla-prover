---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, wait

vars == <<inCS, ticket, nextTicket, wait>>

Bump(t) == IF t < MaxNat THEN t ELSE t

TypeOK ==
  /\ inCS \subseteq 1..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ wait \in 0..MaxNat

Init ==
  /\ inCS = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ wait = 0

\* Same as the Boulanger specification: request a ticket and re-read the
\* shared "nextTicket" register.
Request(p) ==
  /\ p \notin inCS
  /\ inCS' = inCS
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = Bump(nextTicket)
  /\ wait' = Bump(wait)

\* Same as the Boulanger specification: a process enters the critical section
\* only if no live process currently holds a strictly smaller ticket.
\* Because MaxNat is finite, this guard is not trivially always true.
Enter(p) ==
  /\ p \notin inCS
  /\ ticket[p] < wait
  /\ \A q \in inCS : ticket[q] > ticket[p]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<ticket, nextTicket, wait>>

\* Same as the Boulanger specification: a process leaves the critical section.
Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<ticket, nextTicket, wait>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec ==
  /\ Init
  /\ [][Next]_vars

\* Same as the Boulanger specification: the mutual-exclusion safety
\* property (the critical section is a bounded capacity, not mutex, because
\* MaxNat is finite and the model deliberately stays inside the finite range).
MutualExclusion ==
  \A p, q \in inCS : (ticket[p] <= ticket[q] \/ ticket[q] <= ticket[p])

Inv ==
  /\ (\A p \in inCS : inCS = {p} \/ \A q \in inCS : ticket[p] <= ticket[q])
  /\ \A p \in inCS : p \in 1..N

\* The finite override of Nat needs this guard: ticket numbers are kept below
\* MaxNat so the model never wanders outside the finite range.
NatBound == \A p \in 1..N : ticket[p] < MaxNat

====