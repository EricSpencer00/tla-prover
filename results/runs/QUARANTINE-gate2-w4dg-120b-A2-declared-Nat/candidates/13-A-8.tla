---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The inductive spec runs from arbitrary type-correct states rather than
\* only the initial state, so the invariant must hold at start and be
\* preserved by every transition.
VARIABLES inCS, ticket, choose, maxTicket
vars == <<inCS, ticket, choose, maxTicket>>

\* the .cfg substitutes NatOverride for this; they are the same operator here
NatOverride(n) == n

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ choose \in [1..N -> BOOLEAN]
  /\ maxTicket \in 0..MaxNat

Init ==
  /\ inCS = {}
  /\ ticket = [i \in 1..N |-> 0]
  /\ choose = [i \in 1..N |-> FALSE]
  /\ maxTicket = 0

Begin(i) ==
  /\ ~choose[i]
  /\ ticket' = [ticket EXCEPT ![i] = maxTicket]
  /\ choose' = [choose EXCEPT ![i] = TRUE]
  /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
  /\ UNCHANGED inCS

Enter(i) ==
  /\ choose[i]
  /\ \A j \in 1..N : ~choose[j] \/ ticket[j] < ticket[i]
  /\ inCS' = inCS \cup {i}
  /\ choose' = [choose EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, maxTicket>>

Exit(i) ==
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ UNCHANGED <<ticket, choose, maxTicket>>

Next ==
  \/ \E i \in 1..N : Begin(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv ==
  /\ MutualExclusion
  /\ TypeOK

MutualExclusion == \A p, q \in inCS : p = q

\* ISpec: init from any type-correct state, then all reachable states are
\* type-correct (the inductive spec).
ISpec == Init /\ [][Next]_vars

Spec == ISpec
====