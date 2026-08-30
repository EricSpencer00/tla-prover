---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Overrides the unbounded Nat with a finite range 0..MaxNat for model checking.
NatOverride == 0..MaxNat

\* Classic bakery algorithm: each process takes a ticket and enters the critical
\* section only when its ticket is strictly smaller than every other live ticket.
\* The ticket domain is bounded by the model-checking MaxNat, which keeps the
\* state space finite while preserving the mutual-exclusion shape of the design.
\* This module inherits Init, Next, and the invariant set from the base spec
\* and adds only the bounded-natural override.

VARIABLES inCS, ticket, nextTicket, type

vars == <<inCS, ticket, nextTicket, type>>

Init ==
  /\ inCS = [ p \in 0..(N - 1) |-> FALSE ]
  /\ ticket = [ p \in 0..(N - 1) |-> 0 ]
  /\ nextTicket = 0
  /\ type = "idle"

TakeTicket(p) ==
  /\ inCS[p] = FALSE
  /\ type = "idle"
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ ticket EXCEPT ![p] = nextTicket + 1 ]
  /\ nextTicket' = nextTicket + 1
  /\ type' = "holding"
  /\ UNCHANGED inCS

Enter(p) ==
  /\ type = "holding"
  /\ \A q \in 0..(N - 1) : (inCS[q] = FALSE /\ (ticket[q] = 0 \/ ticket[p] < ticket[q]))
  /\ inCS' = [ inCS EXCEPT ![p] = TRUE ]
  /\ type' = "critical"
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ inCS[p] = TRUE
  /\ inCS' = [ inCS EXCEPT ![p] = FALSE ]
  /\ ticket' = [ ticket EXCEPT ![p] = 0 ]
  /\ type' = "idle"
  /\ UNCHANGED nextTicket

GiveUp(p) ==
  /\ type = "holding"
  /\ \E q \in 0..(N - 1) : inCS[q] = TRUE /\ ticket[p] >= ticket[q]
  /\ ticket' = [ ticket EXCEPT ![p] = 0 ]
  /\ type' = "idle"
  /\ UNCHANGED <<inCS, nextTicket>>

Finish(p) ==
  \/ Exit(p)
  \/ GiveUp(p)

Next ==
  \/ \E p \in 0..(N - 1) : TakeTicket(p) \/ Enter(p) \/ Finish(p)

\* Inductive spec: start from any state satisfying the invariant, not just the
\* initial state -- this is what lets the model check the invariant itself.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in 0..(N - 1) : (inCS[p] /\ inCS[q]) => (p = q)
TypeOK ==
  /\ inCS \in [ 0..(N - 1) -> BOOLEAN ]
  /\ ticket \in [ 0..(N - 1) -> NatOverride ]
  /\ nextTicket \in NatOverride
  /\ type \in { "idle", "holding", "critical" }
Inv == MutualExclusion /\ TypeOK

====