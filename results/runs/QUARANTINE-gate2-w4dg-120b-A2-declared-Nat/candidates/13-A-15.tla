---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* A finite bound on the natural numbers used during model checking,
\* overriding the infinite set they come from.
NatOverride == 0..MaxNat

VARIABLES serving, ticket, nextTicket, used

vars == <<serving, ticket, nextTicket, used>>

\* Take one fresh ticket value, wrapping at the maximum.
NewTicket(v) == IF nextTicket < MaxNat THEN v + 1 ELSE 0

InitBakery ==
  /\ serving = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ used = {}

Request(p) ==
  /\ ~ serving[p]
  /\ serving' = [serving EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = NewTicket(nextTicket)]
  /\ nextTicket' = NewTicket(nextTicket)
  /\ used' = used \cup {p}

Enter(p) ==
  /\ serving[p]
  /\ \A q \in used : ticket[p] <= ticket[q]
  /\ UNCHANGED <<serving, ticket, nextTicket, used>>

Exit(p) ==
  /\ serving[p]
  /\ serving' = [serving EXCEPT ![p] = FALSE]
  /\ used' = used \ {p}
  /\ UNCHANGED <<ticket, nextTicket>>

NextBakery ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

\* Inductive specification: any type-correct reachable state may be the start.
ISpec == InitBakery \/ [][NextBakery]_vars

MutualExclusion == \A a, b \in 1..N : (serving[a] /\ serving[b]) => a = b

TypeOK ==
  /\ serving \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride
  /\ used \subseteq (1..N)

Inv == MutualExclusion /\ TypeOK

====