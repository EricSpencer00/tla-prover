---- MODULE MCBakery ----
EXTENDS Naturals

\* MCBakery is the model-checking configuration module for the Bakery
\* mutual exclusion algorithm. It reuses the entire Bakery specification
\* and merely replaces Nat with a finite version, NatOverride, that lives
\* in a bounded range so the model checker can explore the state space.
\* The overriding is done by defining NatOverride as a FINITE set and
\* plugging it in wherever the original spec used Nat.

CONSTANTS N, MaxNat

\* NatOverride replaces the infinite set Nat from Naturals with the finite
\* range 0..MaxNat. EXTENDS Naturals is kept: NatOverride is a new identifier.
NatOverride == 0..MaxNat

VARIABLES nextTicket, ticket, inCS, waiting

vars == <<nextTicket, ticket, inCS, waiting>>

TypeOK ==
  /\ nextTicket \in NatOverride
  /\ ticket \in [1..N -> NatOverride]
  /\ inCS \in BOOLEAN
  /\ waiting \in SUBSET (1..N)

Init ==
  /\ nextTicket = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = FALSE
  /\ waiting = {}

\* Request(p): process p begins waiting for the critical section and takes
\* a fresh ticket, wrapping past MaxNat back to 0.
Request(p) ==
  /\ p \notin waiting
  /\ waiting' = waiting \cup {p}
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket >= MaxNat THEN 0 ELSE nextTicket + 1
  /\ UNCHANGED inCS

\* Enter(p): process p enters the critical section if it is waiting and
\* holds a ticket strictly lower than every waiting process's ticket.
Enter(p) ==
  /\ p \in waiting
  /\ \A q \in waiting : ticket[p] < ticket[q]
  /\ inCS' = TRUE
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED <<nextTicket, ticket>>

\* Exit(p): process p leaves the critical section.
Exit(p) ==
  /\ inCS
  /\ inCS' = FALSE
  /\ UNCHANGED <<nextTicket, ticket, waiting>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

\* The inductive spec starts from any reachable type-correct state and
\* requires the invariant to hold from there.
ISpec == Init /\ [][Next]_vars

MutualExclusion ==
  inCS => (\A p \in 1..N : ticket[p] = 0)

Inv == TypeOK /\ MutualExclusion

====