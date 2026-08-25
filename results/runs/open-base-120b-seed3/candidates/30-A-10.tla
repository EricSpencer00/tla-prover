---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat
       /\ T \in Nat
       /\ F \in Nat
       /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ Bottom \notin Values
       /\ Values # {}

VARIABLES pc, view, prop, est, dec, crashedCount, sent, recv

\* ----------------------------------------------------------------------
\* Helper to compute the maximum of a (possibly empty) set of values
\* ----------------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : v >= w

\* ----------------------------------------------------------------------
\* State initialization
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in 1..N |-> "b1"]
  /\ prop \in [p \in 1..N |-> Values]               \* arbitrary proposals
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ est = [p \in 1..N |-> Bottom]
  /\ dec = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Message == [type : {"p1","p2"}, sender : 1..N, value : Values,
            est : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Phase‑1 actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ LET m == [type |-> "p1", sender |-> p, value |-> prop[p], est |-> Bottom] IN
       sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, prop, est, dec, crashedCount, sent>>

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality({ s \in 1..N : view[p][s] # Bottom }) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][s] : s \in 1..N })]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Phase‑2 actions
\* ----------------------------------------------------------------------
BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ LET m == [type |-> "p2", sender |-> p, value |-> prop[p], est |-> est[p]] IN
       sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pc, view, prop, est, dec, crashedCount, sent>>

Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T
  /\ LET v == CHOOSE w \in Values :
        Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = w }) >= N - T IN
       dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Choosing(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality({ m \in recv[p] : m.type = "p2" }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) < N - T
  /\ LET candidates == { view[p][s] : s \in 1..N /\ view[p][s] # Bottom } IN
       /\ candidates # {}
       /\ dec' = [dec EXCEPT ![p] = CHOOSE w \in candidates]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Crash action
\* ----------------------------------------------------------------------
Crash(p) ==
  /\ pc[p] # "crashed"
  /\ pc[p] # "done"
  /\ crashedCount < F
  /\ crashedCount' = crashedCount + 1
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in 1..N :
    \/ BroadcastPhase1(p)
    \/ \E m \in Message : ReceivePhase1(p,m)
    \/ ComputeEst(p)
    \/ BroadcastPhase2(p)
    \/ \E m \in Message : ReceivePhase2(p,m)
    \/ Decide(p)
    \/ Choosing(p)
    \/ Crash(p)

Spec == Init /\ [][Next]_<<pc, view, prop, est, dec, crashedCount, sent, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [1..N -> {"b1","w1","b2","w2","done","crashed","choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [1..N -> SUBSET Message]

Validity ==
  \A p \in 1..N :
    dec[p] # Bottom => dec[p] \in { prop[s] : s \in 1..N }

Agreement ==
  \A p, q \in 1..N :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

====