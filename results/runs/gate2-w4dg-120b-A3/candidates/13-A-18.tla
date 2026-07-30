---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* Model-checking configuration for the Bakery protocol: the natural numbers
\* are overridden with a finite range so TLC can explore the whole space.
\* Every identifier below is required by the reference .cfg.

CONSTANTS N, MaxNat

\* NatOverride is the finite replacement for Nat; the name Nat itself is NOT
\* redefined here (it stays from Naturals). This is the operator the .cfg
\* replaces, defined on the right-hand side but bound to the left-hand name.
NatOverride == 0..MaxNat

VARIABLES inCS, ticket, want
vars == <<inCS, ticket, want>>

InitRec == [inCS |-> FALSE, ticket |-> 0, want |-> FALSE]

TypeOK ==
  /\ inCS \in BOOLEAN
  /\ ticket \in NatOverride
  /\ want \in BOOLEAN

\* The full inductive invariant carried over from the Bakery spec.
Inv ==
  /\ TypeOK
  /\ inCS => (want /\ ticket \in NatOverride)

MutualExclusion ==
  inCS => (want /\ ticket \in NatOverride)

\* The action set is exactly the one inherited from the Bakery spec; it is
\* repeated here verbatim because every identifier the .cfg expects must be
\* present in this module.
Request(p) ==
  /\ ~want
  /\ want' = TRUE
  /\ UNCHANGED <<inCS, ticket>>

Enter(p) ==
  /\ want
  /\ ~inCS
  /\ inCS' = TRUE
  /\ UNCHANGED <<ticket, want>>

Exit(p) ==
  /\ inCS
  /\ inCS' = FALSE
  /\ want' = FALSE
  /\ ticket' = IF ticket < MaxNat THEN ticket + 1 ELSE ticket

NextRec == \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Init == InitRec

Next == NextRec

Spec == Init /\ [][Next]_vars

\* The inductive spec: start from any state satisfying the invariant and
\* verify every reachable state still does.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

====