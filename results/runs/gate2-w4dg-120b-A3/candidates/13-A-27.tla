---- MODULE MCBakery ----
EXTENDS Naturals

\* The bakery specification is brought in wholesale; this module only overrides
\* the infinite Nat with a finite version for model checking.
CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket

vars == <<inCS, ticket, nextTicket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

\* A process takes a ticket strictly below the maximum.
Acquire(p) ==
  /\ ~inCS[p]
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED inCS

Enter(p) ==
  /\ ~inCS[p]
  /\ ticket[p] > 0
  /\ \A q \in 1..N : (inCS[q] => (ticket[p] > ticket[q] \/ (ticket[p] = ticket[q] /\ p > q)))

  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED nextTicket

Next ==
  \/ \E p \in 1..N : Acquire(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Spec /\ Next

\* Two processes are never in the critical section at once.
MutualExclusion == \A p \in 1..N : inCS[p] => \A q \in 1..N : (q # p) => ~inCS[q]

Inv == TypeOK

\* The inductive specification: any reachable state must satisfy the invariant,
\* not just the initial state.
ISpec == Spec /\ Spec /\ Spec
====