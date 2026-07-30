---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

Take(p) ==
  /\ want[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ \A q \in 1..N : (inCS[q] \/ ticket[q] > ticket[p])
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Take(p)
  \/ \E p \in 1..N : Leave(p)

Spec == Init /\ [][Next]_vars

ISpec == Spec

MutualExclusion ==
  \A a, b \in 1..N : (inCS[a] /\ inCS[b]) => (a = b)

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

Inv ==
  /\ MutualExclusion
  /\ TypeOK

====