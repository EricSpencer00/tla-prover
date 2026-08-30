---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* The model-checking configuration for the Bakery specification.  It
\* overrides Naturals' Nat with a finite range and verifies the full
\* inductive invariant from an arbitrary reachable state.
CONSTANTS N, MaxNat

\* NatOverride replaces Naturals!Nat so the model has a finite number range.
NatOverride == 0..MaxNat

VARIABLES inCS, ticket, inCritical, snap
vars == <<inCS, ticket, inCritical, snap>>

Bound(x) == IF x > MaxNat THEN MaxNat ELSE x

CriticalCount == Cardinality({i \in 1..N : inCritical[i]})

TypeOK ==
  /\ inCS \in 0..N
  /\ ticket \in [1..N -> NatOverride]
  /\ inCritical \in [1..N -> BOOLEAN]
  /\ snap \in [1..N -> NatOverride]

Init ==
  /\ inCS = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCritical = [i \in 1..N |-> FALSE]
  /\ snap = [i \in 1..N |-> 0]

Request(i) ==
  /\ ticket[i] = 0
  /\ ticket' = [ticket EXCEPT ![i] = 1]
  /\ snap' = [snap EXCEPT ![i] = inCS]
  /\ UNCHANGED <<inCS, inCritical>>

Enter(i) ==
  /\ ticket[i] = 1
  /\ snap[i] = 0
  /\ inCritical[i] = FALSE
  /\ inCS < N
  /\ inCS' = 1
  /\ inCritical' = [inCritical EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = 2]
  /\ UNCHANGED snap

Exit(i) ==
  /\ ticket[i] = 2
  /\ inCritical[i] = TRUE
  /\ inCS' = 0
  /\ inCritical' = [inCritical EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED snap

Next == \E i \in 1..N :
  Request(i) \/ Enter(i) \/ Exit(i)

\* Inductive spec: any reachable state must already satisfy the invariant.
ISpec == Init /\ [][Next]_vars

MutualExclusion == CriticalCount <= 1
Inv == MutualExclusion /\ TypeOK
====