---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* The standard Naturals module defines Nat as the infinite set of natural
\* numbers.  For a bounded model, Nat is overridden with a finite carrier,
\* but EXTENDS Naturals is still kept because the rest of the specification
\* depends on the arithmetic operators it supplies.
NatOverride == { n \in 0..MaxNat : TRUE }

VARIABLES requesting, responding, owned, ticket

vars == << requesting, responding, owned, ticket >>

Init ==
  /\ requesting = {}
  /\ responding = {}
  /\ owned = [p \in 1..N |-> 0]
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ p \notin requesting
  /\ p \notin responding
  /\ owned[p] = 0
  /\ requesting' = requesting \cup {p}
  /\ UNCHANGED << responding, owned, ticket >>

Enter(p) ==
  /\ p \in requesting
  /\ requesting' = requesting \ {p}
  /\ responding' = responding \cup {p}
  /\ UNCHANGED << owned, ticket >>

Take(p) ==
  /\ p \in responding
  /\ owned[p] = 0
  /\ \A q \in 1..N : owned[q] # p
  /\ owned' = [owned EXCEPT ![p] = 1]
  /\ responding' = responding \ {p}
  /\ UNCHANGED << requesting, ticket >>

Leave(p) ==
  /\ owned[p] = 1
  /\ owned' = [owned EXCEPT ![p] = 0]
  /\ UNCHANGED << requesting, responding, ticket >>

Bump(p) ==
  /\ p \notin requesting
  /\ p \notin responding
  /\ owned[p] = 0
  /\ ticket[p] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
  /\ UNCHANGED << requesting, responding, owned >>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Take(p)
  \/ \E p \in 1..N : Leave(p)
  \/ \E p \in 1..N : Bump(p)

Spec ==
  /\ Init
  /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (owned[p] = 1 /\ owned[q] = 1) => p = q

TypeOK ==
  /\ requesting \subseteq (1..N)
  /\ responding \subseteq (1..N)
  /\ owned \in [1..N -> {0, 1}]
  /\ ticket \in [1..N -> 0..MaxNat]

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p \in 1..N : ticket[p] < MaxNat

StateConstraint ==
  \A p \in 1..N : ticket[p] < MaxNat

====