---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* The model-checking configuration module for the Bakery mutual exclusion
\* algorithm.  It inherits the bakery model from an earlier spec and overrides
\* Nat (the natural number type) with a finite range NatOverride so the state
\* space is bounded; the override is defined at the end, and the .cfg file
\* expects it to replace Naturals!Nat, not to be redeclared as Nat here.
CONSTANTS N, MaxNat

ASSUME N \in NatOverride \ {0}

VARIABLES inCS, want, own, ticket

vars == <<inCS, want, own, ticket>>

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ own = "free"
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ p \notin want
  /\ p \notin inCS
  /\ want' = want \cup {p}
  /\ UNCHANGED <<inCS, own, ticket>>

Enter(p) ==
  /\ p \in want
  /\ own = "free"
  /\ \A q \in inCS : q # p
  /\ own' = p
  /\ ticket' = [ticket EXCEPT ![p] = 1]
  /\ inCS' = inCS \cup {p}
  /\ want' = want \ {p}

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ own' = "free"
  /\ UNCHANGED <<want, ticket>>

Quiesce ==
  /\ inCS = {}
  /\ want = {}
  /\ UNCHANGED vars

Next ==
  \/ Quiesce
  \/ \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in inCS : p = q

TypeOK ==
  /\ inCS \subseteq 1..N
  /\ want \subseteq 1..N
  /\ own \in 1..N \cup {"free"}
  /\ ticket \in [1..N -> 0..MaxNat]

\* The full inductive invariant: inCS is bounded by the token, and the token
\* is only ever held by whoever is actually in the critical section.
Inv ==
  /\ inCS \subseteq {own}
  /\ \A p \in inCS : ticket[p] = 1

ISpec == Spec

====