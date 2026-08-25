---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PCVals == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}

Message == [type : {"p1", "p2"},
            sender : 1..N,
            value  : Values,
            est    : Values]   \* for p1 messages, est = Bottom

Max(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : v >= w

DistinctSenders(i) == { j \in 1..N : view[i][j] # Bottom }

ReceivedEnoughPhase1(i) == Cardinality(DistinctSenders(i)) >= N - T

Estimated(i) == 
  IF DistinctSenders(i) = {} THEN Bottom
  ELSE Max({ view[i][j] : j \in 1..N })

SameEstCount(i, v) == Cardinality({ j \in 1..N : view[i][j] = v }) >= N - T

ReceivedAllPhase2(i) == \A j \in 1..N : view[i][j] # Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* [i \in 1..N |-> location]
          prop,             \* [i \in 1..N |-> proposed value]
          view,             \* [i \in 1..N |-> [j \in 1..N |-> Values]]
          est,              \* [i \in 1..N |-> Values]   (estimated after phase‑1)
          dec,              \* [i \in 1..N |-> Values]   (decision)
          crashedCount,     \* Nat
          msgs              \* SUBSET Message

vars == << pc, prop, view, est, dec, crashedCount, msgs >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in 1..N |-> "b1"]
  /\ prop \in [i \in 1..N |-> Values]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ est = [i \in 1..N |-> Bottom]
  /\ dec = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ msgs = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastP1(i) ==
  /\ pc[i] = "b1"
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ msgs' = msgs \cup {[type |-> "p1",
                         sender |-> i,
                         value  |-> prop[i],
                         est    |-> Bottom]} 
  /\ UNCHANGED << prop, view, est, dec, crashedCount >>

BroadcastP2(i) ==
  /\ pc[i] = "b2"
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ msgs' = msgs \cup {[type |-> "p2",
                         sender |-> i,
                         value  |-> prop[i],
                         est    |-> est[i]}] 
  /\ UNCHANGED << prop, view, dec, crashedCount >>

ReceiveP1(i) ==
  /\ pc[i] = "w1"
  /\ \E m \in msgs :
        /\ m.type = "p1"
        /\ view[i][m.sender] = Bottom
        /\ view' = [view EXCEPT ![i][m.sender] = m.value]
        /\ UNCHANGED << pc, prop, msgs, est, dec, crashedCount >>
  /\ UNCHANGED view

ReceiveP2(i) ==
  /\ pc[i] = "w2"
  /\ \E m \in msgs :
        /\ m.type = "p2"
        /\ view[i][m.sender] = Bottom
        /\ view' = [view EXCEPT ![i][m.sender] = m.est]
        /\ UNCHANGED << pc, prop, msgs, est, dec, crashedCount >>
  /\ UNCHANGED view

ComputeEst(i) ==
  /\ pc[i] = "w1"
  /\ ReceivedEnoughPhase1(i)
  /\ pc' = [pc EXCEPT ![i] = "b2"]
  /\ est' = [est EXCEPT ![i] = Estimated(i)]
  /\ UNCHANGED << prop, view, msgs, dec, crashedCount >>

DecideFromEst(i) ==
  /\ pc[i] = "w2"
  /\ \E v \in Values : SameEstCount(i, v)
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ dec' = [dec EXCEPT ![i] = v]
  /\ UNCHANGED << prop, view, msgs, est, crashedCount >>

MoveToChoosing(i) ==
  /\ pc[i] = "w2"
  /\ ReceivedAllPhase2(i)
  /\ ~\E v \in Values : SameEstCount(i, v)
  /\ pc' = [pc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED << prop, view, msgs, est, dec, crashedCount >>

ChooseAndDecide(i) ==
  /\ pc[i] = "choosing"
  /\ \E v \in Values :
        v \in { view[i][j] : j \in 1..N }
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ dec' = [dec EXCEPT ![i] = v]
  /\ UNCHANGED << prop, view, msgs, est, crashedCount >>

Crash(i) ==
  /\ pc[i] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << prop, view, msgs, est, dec >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E i \in 1..N : BroadcastP1(i)
  \/ \E i \in 1..N : BroadcastP2(i)
  \/ \E i \in 1..N : ReceiveP1(i)
  \/ \E i \in 1..N : ReceiveP2(i)
  \/ \E i \in 1..N : ComputeEst(i)
  \/ \E i \in 1..N : DecideFromEst(i)
  \/ \E i \in 1..N : MoveToChoosing(i)
  \/ \E i \in 1..N : ChooseAndDecide(i)
  \/ \E i \in 1..N : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ N \in Nat
  /\ T \in Nat
  /\ F \in Nat
  /\ 2 * T < N
  /\ F <= T
  /\ N > 0
  /\ Bottom \notin Values
  /\ pc \in [1..N -> PCVals]
  /\ prop \in [1..N -> Values]
  /\ view \in [1..N -> [1..N -> Values]]
  /\ est \in [1..N -> Values]
  /\ dec \in [1..N -> Values]
  /\ crashedCount \in Nat
  /\ msgs \subseteq Message

Validity ==
  \A i \in 1..N :
    dec[i] # Bottom => dec[i] \in { prop[j] : j \in 1..N }

Agreement ==
  \A i, j \in 1..N :
    /\ dec[i] # Bottom
    /\ dec[j] # Bottom
    => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM SpecImpliesTypeOK == Spec => []TypeOK
THEOREM SpecImpliesValidity == Spec => []Validity
THEOREM SpecImpliesAgreement == Spec => []Agreement

====