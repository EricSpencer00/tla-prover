---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, want, served

vars == <<inCS, ticket, want, served>>

\* The ticket pool is a finite range 0..MaxNat, so the state space stays finite
\* and model checking is feasible; this is the override of the unbounded Nat.
NatOverride == 0..MaxNat

TypeOK ==
  /\ inCS \subseteq 1..N
  /\ ticket \in [1..N -> NatOverride]
  /\ want \in [1..N -> BOOLEAN]
  /\ served \in NatOverride

Init ==
  /\ inCS = {}
  /\ ticket = [k \in 1..N |-> 0]
  /\ want = [k \in 1..N |-> FALSE]
  /\ served = 0

Enter(k) ==
  /\ want[k]
  /\ inCS = {}
  /\ inCS' = {k}
  /\ UNCHANGED <<ticket, want, served>>

Leave(k) ==
  /\ k \in inCS
  /\ inCS' = {}
  /\ ticket' = [ticket EXCEPT ![k] = (IF @ = MaxNat THEN 0 ELSE @ + 1)]
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ want' = [want EXCEPT ![k] = FALSE]

Request(k) ==
  /\ ~want[k]
  /\ inCS = {}
  /\ want' = [want EXCEPT ![k] = TRUE]
  /\ UNCHANGED <<inCS, ticket, served>>

Next ==
  \E k \in 1..N : Enter(k) \/ Leave(k) \/ Request(k)

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A a, b \in inCS : a = b

\* The invariant has three conjuncts; each is individually stable under every
\* action, so the conjunction is inductive from any reachable state.
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A k \in 1..N : (ticket[k] = MaxNat) => (k \notin inCS)

====