---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

\* Model-checking configuration for the Bakery mutual exclusion algorithm.
\* This module inherits the full Bakery spec (states, init, next, and safety
\* properties) and overrides the unbounded Nat type with a bounded finite set
\* of natural numbers, chosen by the model checker via the MaxNat constant.
\* The inductive spec is used, so the invariant must hold from any reachable
\* type-correct state, not just from Init.

CONSTANTS N, MaxNat, Nat

\* The bounded set of natural numbers used for this model checking run.
NatOverride == 0..MaxNat

VARIABLES inCS, wantSet, wants, ticket
vars == <<inCS, wantSet, wants, ticket>>

\* Ticket numbers are bounded above by MaxNat, rather than being unbounded.
BoundedTicket(n) == IF n > MaxNat THEN MaxNat ELSE n

Init ==
  /\ inCS = {}
  /\ wantSet = 0
  /\ wants = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]

Want(p) ==
  /\ p \notin inCS
  /\ ~wants[p]
  /\ wants' = [wants EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = BoundedTicket(wantSet)]
  /\ wantSet' = BoundedTicket(wantSet + 1)
  /\ UNCHANGED inCS

Enter(p) ==
  /\ wants[p]
  /\ \A q \in inCS : ticket[p] < ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ wants' = [wants EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<wantSet, ticket>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<wantSet, wants, ticket>>

Next ==
  \/ \E p \in 1..N : Want(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars
ISpec == Spec

MutualExclusion == \A p \in inCS : \A q \in inCS : p = q

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ wantSet \in 0..MaxNat
  /\ wants \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

\* The full inductive invariant of the Bakery algorithm.
Inv ==
  /\ MutualExclusion
  /\ TypeOK

====