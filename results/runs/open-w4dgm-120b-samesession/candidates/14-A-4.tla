---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, served, servedBy

vars == <<inCS, want, ticket, served, servedBy>>

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ served = 0
  /\ servedBy = 0

Request(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, ticket, served, servedBy>>

Enter(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = served + 1]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<served, servedBy>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ served' = ticket[p]
  /\ servedBy' = p
  /\ UNCHANGED <<want, ticket>>

Next ==
  \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ served \in 0..MaxNat
  /\ servedBy \in 0..N

Inv ==
  /\ \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q
  /\ served <= MaxNat
  /\ servedBy \in 0..N
  /\ served \in 0..MaxNat
  /\ \A p, q \in 1..N : (want[p] /\ want[q]) => p = q

TicketBound ==
  \A p \in 1..N : ticket[p] < MaxNat

====