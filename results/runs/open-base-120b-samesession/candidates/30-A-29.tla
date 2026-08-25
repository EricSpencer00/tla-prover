---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* =====================================================================
\* Process set and message type
\* =====================================================================
Proc == 1..N

Message == [type : {"Phase1","Phase2"},
            val  : Values,
            sender : Proc,
            est  : Values \cup {Bottom}]

\* =====================================================================
\* Variables
\* =====================================================================
VARIABLES pc, view, prop, est, dec, crashedCount, sent, rcv

vars == << pc, view, prop, est, dec, crashedCount, sent, rcv >>

\* =====================================================================
\* Helper definitions
\* =====================================================================
\* Maximum of a non‑empty set of values (Values are totally ordered)
MaxVal(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* Number of distinct senders from which p has received a Phase‑1 message
RecvPhase1Senders(p) ==
  { m.sender : m \in rcv[p] /\ m.type = "Phase1" }

\* Number of messages of Phase‑2 with a given estimated value
RecvPhase2Count(p, v) ==
  Cardinality({ m \in rcv[p] : m.type = "Phase2" /\ m.est = v })

\* =====================================================================
\* Initial state
\* =====================================================================
Init ==
  /\ pc = [p \in Proc |-> "b1"]                                   \* broadcast phase 1
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]                                   \* nondeterministic proposal
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ rcv = [p \in Proc |-> {}]

\* =====================================================================
\* Actions
\* =====================================================================
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ let m == [type |-> "Phase1", val |-> prop[p],
              sender |-> p, est |-> Bottom] in
     /\ sent' = sent \cup {m}
     /\ pc' = [pc EXCEPT ![p] = "w1"]
     /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

ReceivePhase1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "Phase1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(RecvPhase1Senders(p)) >= N - T
  /\ LET vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
     est' = [est EXCEPT ![p] = MaxVal(vals)]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, rcv >>

BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ let m == [type |-> "Phase2", val |-> prop[p],
              sender |-> p, est |-> est[p]] in
     /\ sent' = sent \cup {m}
     /\ pc' = [pc EXCEPT ![p] = "w2"]
     /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

ReceivePhase2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "Phase2"
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        RecvPhase2Count(p, v) >= N - T
  /\ let v == CHOOSE w \in Values : RecvPhase2Count(p, w) >= N - T in
     /\ dec' = [dec EXCEPT ![p] = v]
     /\ pc' = [pc EXCEPT ![p] = "done"]
     /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

Choose(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality({ m \in rcv[p] : m.type = "Phase2" }) = N
  /\ \A v \in Values : RecvPhase2Count(p, v) < N - T
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
     /\ candidates # {}
     /\ dec' = [dec EXCEPT ![p] = CHOOSE w \in candidates : TRUE]
     /\ pc' = [pc EXCEPT ![p] = "done"]
     /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

Crash(p) ==
  /\ crashedCount < F
  /\ pc[p] # "crashed"
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, rcv >>

\* =====================================================================
\* Next-state relation
\* =====================================================================
Next ==
  \E p \in Proc :
    \/ BroadcastPhase1(p)
    \/ \E m \in Message : ReceivePhase1(p, m)
    \/ ComputeEst(p)
    \/ BroadcastPhase2(p)
    \/ \E m \in Message : ReceivePhase2(p, m)
    \/ Decide(p)
    \/ Choose(p)
    \/ Crash(p)

\* =====================================================================
\* Specification
\* =====================================================================
Spec == Init /\ [][Next]_vars

\* =====================================================================
\* Type correctness invariant
\* =====================================================================
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choose"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ rcv \in [Proc -> SUBSET Message]

\* =====================================================================
\* Safety properties
\* =====================================================================
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => dec[p] \in Values /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* =====================================================================
\* The required identifiers for the configuration file
\* =====================================================================
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====