---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket, snap

vars == <<inCS, want, ticket, nextTicket, snap>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ snap \in [1..N -> 0..MaxNat]

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ snap = [p \in 1..N |-> 0]

Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ snap' = [snap EXCEPT ![p] = nextTicket]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ snap[p] = nextTicket
  /\ \A q \in 1..N : ~inCS[q]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED snap

Leave(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, ticket, nextTicket, snap>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Leave(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
  /\ MutualExclusion
  /\ TypeOK

FiniteBound == \A p \in 1..N : ticket[p] < MaxNat

====