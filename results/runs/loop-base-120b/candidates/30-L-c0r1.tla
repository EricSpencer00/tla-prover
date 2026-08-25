---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Assumptions on the constants
\* ----------------------------------------------------------------------
ASSUME 0 < N
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME Bottom \notin Values
ASSUME Values /= {}

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"phase1", "phase2"},
            value : Values,
            sender : Proc,
            est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N->N matrix of observed values
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          dec,              \* decision value
          crashed,          \* set of crashed processes
          sent,             \* set of all messages that have been sent
          recv              \* messages received by each process

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
BroadcastPhase1 == "b1"
WaitPhase1      == "w1"
BroadcastPhase2 == "b2"
WaitPhase2      == "w2"
Choose          == "choose"
Done            == "done"
Crashed         == "crashed"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxVal(S) == IF S = {} THEN Bottom ELSE Max(S)

ReceivedFrom(i, typ) ==
  { m \in recv[i] : m.type = typ }

ReceivedFromPhase1(i) == ReceivedFrom(i, "phase1")
ReceivedFromPhase2(i) == ReceivedFrom(i, "phase2")

CountEst(i, v) ==
  Cardinality({ m \in ReceivedFromPhase2(i) : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> BroadcastPhase1]
  /\ prop \in [Proc -> Values]               \* each process proposes a value
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1Action(i) ==
  /\ pc[i] = BroadcastPhase1
  /\ pc' = [pc EXCEPT ![i] = WaitPhase1]
  /\ sent' = sent \cup { [type |-> "phase1",
                         value |-> prop[i],
                         sender |-> i,
                         est   |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashed, recv >>

ReceivePhase1Action(i, m) ==
  /\ pc[i] = WaitPhase1
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.sender \notin { msg.sender : msg \in recv[i] }
  /\ view' = [view EXCEPT ![i][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

Phase1ToPhase2(i) ==
  /\ pc[i] = WaitPhase1
  /\ Cardinality({ j \in Proc : view[i][j] # Bottom }) >= N - T
  /\ LET e == MaxVal({ view[i][j] : j \in Proc }) IN
        /\ est' = [est EXCEPT ![i] = e]
        /\ pc'  = [pc EXCEPT ![i] = BroadcastPhase2]
        /\ sent' = sent \cup { [type |-> "phase2",
                               value |-> prop[i],
                               sender |-> i,
                               est   |-> e] }
        /\ UNCHANGED << view, prop, dec, crashed, recv >>

BroadcastPhase2Action(i) ==
  /\ pc[i] = BroadcastPhase2
  /\ pc' = [pc EXCEPT ![i] = WaitPhase2]
  /\ UNCHANGED << view, prop, est, dec, crashed, sent, recv >>

ReceivePhase2Action(i, m) ==
  /\ pc[i] = WaitPhase2
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m.sender \notin { msg.sender : msg \in recv[i] }
  /\ view' = [view EXCEPT ![i][m.sender] = m.est]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashed, sent >>

DecideAction(i, v) ==
  /\ pc[i] = WaitPhase2
  /\ CountEst(i, v) >= N - T
  /\ dec' = [dec EXCEPT ![i] = v]
  /\ pc'  = [pc EXCEPT ![i] = Done]
  /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

MoveToChoose(i) ==
  /\ pc[i] = WaitPhase2
  /\ Cardinality(ReceivedFromPhase2(i)) = N
  /\ \A v \in Values : CountEst(i, v) < N - T
  /\ pc' = [pc EXCEPT ![i] = Choose]
  /\ UNCHANGED << view, prop, est, dec, crashed, sent, recv >>

ChooseAction(i) ==
  /\ pc[i] = Choose
  /\ LET candidates == { view[i][j] : j \in Proc /\ view[i][j] # Bottom } IN
        /\ candidates # {}
        /\ LET v == MaxVal(candidates) IN
              /\ dec' = [dec EXCEPT ![i] = v]
              /\ pc'  = [pc EXCEPT ![i] = Done]
              /\ UNCHANGED << view, prop, est, crashed, sent, recv >>

CrashAction(i) ==
  /\ i \notin crashed
  /\ Cardinality(crashed) < F
  /\ pc' = [pc EXCEPT ![i] = Crashed]
  /\ crashed' = crashed \cup {i}
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E i \in Proc : BroadcastPhase1Action(i)
  \/ \E i \in Proc, m \in Message : ReceivePhase1Action(i, m)
  \/ \E i \in Proc : Phase1ToPhase2(i)
  \/ \E i \in Proc : BroadcastPhase2Action(i)
  \/ \E i \in Proc, m \in Message : ReceivePhase2Action(i, m)
  \/ \E i \in Proc, v \in Values : DecideAction(i, v)
  \/ \E i \in Proc : MoveToChoose(i)
  \/ \E i \in Proc : ChooseAction(i)
  \/ \E i \in Proc : CrashAction(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","choose","done","crashed"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashed \subseteq Proc
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A i \in Proc : dec[i] # Bottom => dec[i] \in Values

Agreement ==
  \A i, j \in Proc :
    (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Validity
INVARIANT Agreement

====