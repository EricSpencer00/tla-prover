---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Phase == {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}

Message == [type : {"phase1", "phase2"},
            value : Values,
            sender : Proc,
            est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashedCount, sent, recv

vars == << pc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Phase1Senders(p) == { m.sender : m \in recv[p] /\ m.type = "phase1" }

Phase2Senders(p) == { m.sender : m \in recv[p] /\ m.type = "phase2" }

Phase2EstCount(p, v) ==
  Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v })

ReceivedAllPhase2(p) == Phase2Senders(p) = Proc

ReceivedEnoughEst(p, v) == Phase2EstCount(p, v) >= N - T

MaxValue(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

ValuesFromView(p) ==
  { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Broadcast phase‑1
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ sent' = sent \cup { [type |-> "phase1",
                         value |-> prop[p],
                         sender |-> p,
                         est   |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

\* Receive a phase‑1 message
ReceivePhase1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m \notin recv[p]          \* avoid duplicate reception
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

\* Transition to phase‑2 after enough phase‑1 messages
ToPhase2(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(Phase1Senders(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ est' = [est EXCEPT ![p] = MaxValue({ view[p][q] : q \in Proc })]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

\* Broadcast phase‑2
BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ sent' = sent \cup { [type |-> "phase2",
                         value |-> prop[p],
                         sender |-> p,
                         est   |-> est[p]] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

\* Receive a phase‑2 message
ReceivePhase2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

\* Decide when enough identical estimates are seen
DecideFromEst(p, v) ==
  /\ pc[p] = "w2"
  /\ ReceivedEnoughEst(p, v)
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

\* Move to choosing state when all phase‑2 messages received
MoveToChoosing(p) ==
  /\ pc[p] = "w2"
  /\ ReceivedAllPhase2(p)
  /\ \A v \in Values : ~ReceivedEnoughEst(p, v)   \* no majority estimate
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

\* Choose a value from the local view and decide
ChooseAndDecide(p) ==
  /\ pc[p] = "choosing"
  /\ ValuesFromView(p) # {}
  /\ LET v == CHOOSE w \in ValuesFromView(p) : TRUE IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

\* Crash a process (if fault budget not exceeded)
Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ BroadcastPhase1(p)
    \/ \E m \in sent : ReceivePhase1(p, m)
    \/ ToPhase2(p)
    \/ BroadcastPhase2(p)
    \/ \E m \in sent : ReceivePhase2(p, m)
    \/ \E v \in Values : DecideFromEst(p, v)
    \/ MoveToChoosing(p)
    \/ ChooseAndDecide(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> Phase]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    IF dec[p] # Bottom
    THEN dec[p] \in Values /\ \E q \in Proc : prop[q] = dec[p]
    ELSE TRUE

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====