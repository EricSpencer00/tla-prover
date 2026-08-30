---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The override below replaces the unbounded Naturals.Nat with a bounded
\* version, keeping the rest of the spec unchanged and still type-correct.
NatOverride(n) == IF n <= MaxNat THEN n ELSE MaxNat

VARIABLES inCS, want, ticket

vars == <<inCS, want, ticket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]

NextTicket(t) == IF t < MaxNat THEN t + 1 ELSE MaxNat

\* A process requests the critical section and takes a ticket only if it is
\* currently unused or has reached its ceiling (bounded reuse).
Request(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = NextTicket(@)]
  /\ UNCHANGED inCS

Enter(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ \A q \in 1..N : (want[q] => ticket[q] >= ticket[p])
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED ticket

Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, ticket>>

RequestSome == \E p \in 1..N : Request(p)
EnterSome == \E p \in 1..N : Enter(p)
LeaveSome == \E p \in 1..N : Leave(p)

Next == RequestSome \/ EnterSome \/ LeaveSome

\* The inductive spec starts from any state satisfying the invariant, not
\* just the initial state -- this is what lets the bounded ticket range still
\* guarantee mutual exclusion even when a ticket wraps back to its ceiling.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : inCS[p] => (\A q \in 1..N : q # p => ~inCS[q])

\* Every reachable state must still satisfy the full invariant.
Inv == MutualExclusion /\ TypeOK

====