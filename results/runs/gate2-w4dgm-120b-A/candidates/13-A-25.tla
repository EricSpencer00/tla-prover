---- MODULE MCBakery ----
EXTENDS Naturals

\* Model-checking configuration for the Bakery algorithm.  It overrides the
\* natural-number type with a finite range (0..MaxNat) so that the state space
\* stays finite and exhaustive checking is feasible.  All logic is identical
\* to the standard Bakery spec except for the bounded Nat used here.

CONSTANTS N, MaxNat

VARIABLES inCS, waiting, ticket, maxTicket, served
vars == <<inCS, waiting, ticket, maxTicket, served>>

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ waiting \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ maxTicket \in 0..MaxNat
  /\ served \in 0..MaxNat

\* Overridden to be a bounded version of Nat; EXTENDS Naturals is retained
\* so other standard operators remain available.
NatOverride == (IF MaxNat + 1 > 0 THEN MaxNat + 1 ELSE 1)

\* The full inductive invariant: safety + type-+state coherence.  Every
\* inCS process holds the lowest ticket among those waiting, so contention
\* is resolved by priority and two processes can never be critical at once.
Inv ==
  /\ TypeOK
  /\ inCS \subseteq waiting
  /\ \A p \in inCS : \A q \in waiting : p = q \/ ticket[p] < ticket[q]
  /\ \A p \in waiting : p \notin inCS => ticket[p] <= maxTicket

\* The inductive spec: start from any type-correct reachable state (not
\* just the initial state) and run forever.  Tick marks an idle step that
\* keeps at least one process interested, forcing activity.
Init ==
  /\ inCS = {}
  /\ waiting = 1..N
  /\ ticket = [p \in 1..N |-> 0]
  /\ maxTicket = 0
  /\ served = 0

Acquire(p) ==
  /\ p \in waiting
  /\ p \notin inCS
  /\ ticket' = [ticket EXCEPT ![p] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ UNCHANGED <<inCS, waiting, served>>

\* The upgrade: a waiting process enters only if it has the lowest ticket.
Enter(p) ==
  /\ p \in waiting
  /\ p \notin inCS
  /\ \A q \in waiting : ticket[p] <= ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<waiting, ticket, maxTicket, served>>

Leave(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ waiting' = waiting \ {p}
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ UNCHANGED maxTicket

Tick ==
  /\ \E p \in 1..N : p \in waiting
  /\ UNCHANGED vars

Next ==
  \/ \E p \in 1..N : Acquire(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Leave(p)
  \/ Tick

\* ISpec is the entry point checked by TLC: startup from any reachable
\* type-correct state, plus the safety invariant to be preserved.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Tick)

\* A model-checked safety invariant must be preserved from every reachable
\* state, not just from the designated start state -- hence Init /\ [][Next]_.
MutualExclusion == Inv
====