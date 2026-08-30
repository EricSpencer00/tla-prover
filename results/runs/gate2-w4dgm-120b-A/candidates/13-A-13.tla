---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket

vars == <<inCS, want, ticket>>

MaxTicket == MaxNat

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ want \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxTicket]
  /\ Cardinality(inCS) <= 1

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
  /\ p \notin want
  /\ p \notin inCS
  /\ want' = want \cup {p}
  /\ UNCHANGED <<inCS, ticket>>

Enter(p) ==
  /\ p \in want
  /\ inCS = {}
  /\ ticket' = [ticket EXCEPT ![p] = MaxTicket]
  /\ inCS' = {p}
  /\ want' = want \ {p}

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = {}
  /\ UNCHANGED <<want, ticket>>

Reset(p) ==
  /\ p \notin inCS
  /\ ticket[p] = MaxTicket
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<inCS, want>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Reset(p)

MutualExclusion == \A a, b \in inCS : a = b

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

====