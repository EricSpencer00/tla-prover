---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The finite set of natural numbers over which model checking ranges:
\* this is exactly what the .cfg file replaces the infinite Naturals.Nat
\* set with, so the model checker never has to explore ticket numbers
\* above the configured maximum.
NatOverride == 0..MaxNat

VARIABLES inCS, ticket, request

vars == <<inCS, ticket, request>>

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ request = [i \in 1..N |-> FALSE]

Request(i) ==
  /\ ~request[i]
  /\ request' = [request EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket>>

Acquire(i) ==
  /\ request[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ \A j \in 1..N : ticket[j] < ticket[i]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, request>>

Release(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ request' = [request EXCEPT ![i] = FALSE]
  /\ UNCHANGED ticket

Ticket(i) ==
  /\ request[i]
  /\ inCS[i]
  /\ ticket[i] < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = @ + 1]
  /\ UNCHANGED <<inCS, request>>

Next ==
  \E i \in 1..N : Request(i) \/ Acquire(i) \/ Release(i) \/ Ticket(i)

Spec == Init /\ [][Next]_vars
ISpec == Spec

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ request \in [1..N -> BOOLEAN]

Inv == MutualExclusion /\ TypeOK

====