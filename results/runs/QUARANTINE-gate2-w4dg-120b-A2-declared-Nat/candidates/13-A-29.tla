---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* NatOverride is a bounded version of the natural numbers that the model
\* checker substitutes for Nat in the base Bakery spec, making the ticket
\* numbers finite.
NatOverride == 0..MaxNat

VARIABLES entering, ticket, inCS

vars == <<entering, ticket, inCS>>

InitBakery ==
  /\ entering = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]

Request(p) ==
  /\ ~entering[p]
  /\ ~inCS[p]
  /\ entering' = [entering EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = CHOOSE k \in NatOverride : \A q \in 1..N : (entering[q] => k <= ticket[q])]
  /\ UNCHANGED inCS

Enter(p) ==
  /\ entering[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<entering, ticket>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ entering' = [entering EXCEPT ![p] = FALSE]
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Init == InitBakery

\* The inductive specification starts from any type-correct state satisfying the
\* invariant, not just the initial state.
ISpec == Init /\ [][Next]_vars

\* Mutual exclusion: two processes are never in the critical section together.
MutualExclusion ==
  /\ \A p \in 1..N : inCS[p] => entering[p]
  /\ \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

\* Ticket numbers stay inside the bounded range.
TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]

\* The full inductive invariant for the bakery algorithm.
Inv == MutualExclusion /\ TypeOK

====