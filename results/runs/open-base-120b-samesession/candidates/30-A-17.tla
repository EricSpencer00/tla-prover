---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Process == 1..N

Message == [type : {"phase1", "phase2"},
            value: Values,
            sender: Process,
            est   : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Bcst1    == "bcast1"
Wait1   == "wait1"
Bcst2   == "bcast2"
Wait2   == "wait2"
Choosing == "choosing"
Done    == "done"
Crashed == "crashed"

ControlLoc == {Bcst1, Wait1, Bcst2, Wait2, Choosing, Done, Crashed}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,                 \* [p \in Process -> ControlLoc]
          prop,               \* [p \in Process -> Values]
          view,               \* [p \in Process -> [q \in Process -> Values \cup {Bottom}]]
          est,                \* [p \in Process -> Values \cup {Bottom}]
          decision,           \* [p \in Process -> Values \cup {Bottom}]
          crashedCount,       \* Nat
          sent,               \* SUBSET Message
          recv                \* [p \in Process -> SUBSET Message]

vars == << pc, prop, view, est, decision, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
MaxInSet(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : w <= v

SendPhase1(p) ==
  [type |-> "phase1",
   value |-> prop[p],
   sender |-> p,
   est |-> Bottom]

SendPhase2(p) ==
  [type |-> "phase2",
   value |-> prop[p],
   sender |-> p,
   est |-> est[p]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Process |-> Bcst1]
  /\ prop \in [Process -> Values]
  /\ view = [p \in Process |-> [q \in Process |-> Bottom]]
  /\ est = [p \in Process |-> Bottom]
  /\ decision = [p \in Process |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Process |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = Bcst1
  /\ pc' = [pc EXCEPT ![p] = Wait1]
  /\ sent' = sent \cup { SendPhase1(p) }
  /\ UNCHANGED << prop, view, est, decision, crashedCount, recv >>

ReceivePhase1(p, m) ==
  /\ pc[p] = Wait1
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.sender \in Process
  /\ m \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, decision, crashedCount, sent >>

ComputeEst(p) ==
  /\ pc[p] = Wait1
  /\ Cardinality({ s \in Process : view[p][s] # Bottom }) >= N - T
  /\ let vals == { view[p][s] : s \in Process /\ view[p][s] # Bottom } in
     est' = [est EXCEPT ![p] = MaxInSet(vals)]
  /\ pc' = [pc EXCEPT ![p] = Bcst2]
  /\ UNCHANGED << prop, view, decision, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
  /\ pc[p] = Bcst2
  /\ pc' = [pc EXCEPT ![p] = Wait2]
  /\ sent' = sent \cup { SendPhase2(p) }
  /\ UNCHANGED << prop, view, est, decision, crashedCount, recv >>

ReceivePhase2(p, m) ==
  /\ pc[p] = Wait2
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m.sender \in Process
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, view, est, decision, crashedCount, sent >>

DecideFromEst(p) ==
  /\ pc[p] = Wait2
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] :
                       m.type = "phase2" /\ m.est = v }) >= N - T
  /\ LET v == CHOOSE w \in Values :
                Cardinality({ m \in recv[p] :
                               m.type = "phase2" /\ m.est = w }) >= N - T
     IN
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = Done]
  /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
  /\ pc[p] = Wait2
  /\ Cardinality({ m \in recv[p] : m.type = "phase2" }) = N   \* all senders reached
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = Choosing]
  /\ UNCHANGED << prop, view, est, decision, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
  /\ pc[p] = Choosing
  /\ LET vals == { view[p][s] : s \in Process /\ view[p][s] # Bottom } IN
        vals # {}   \* there is at least one value seen
  /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in vals : TRUE]  \* deterministic arbitrary choice
  /\ pc' = [pc EXCEPT ![p] = Done]
  /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ crashedCount < F
  /\ pc[p] # Crashed
  /\ pc' = [pc EXCEPT ![p] = Crashed]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << prop, view, est, decision, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Process :
    \/ BroadcastPhase1(p)
    \/ ReceivePhase1(p, m)          \* m quantified below
    \/ ComputeEst(p)
    \/ BroadcastPhase2(p)
    \/ ReceivePhase2(p, m)          \* m quantified below
    \/ DecideFromEst(p)
    \/ MoveToChoosing(p)
    \/ ChooseAndDecide(p)
    \/ Crash(p)

\* Since Receive actions need a concrete message, we expand them with existential quantification
ReceivePhase1(p, m) == 
  /\ \E m \in Message : 
        /\ pc[p] = Wait1
        /\ m \in sent
        /\ m.type = "phase1"
        /\ m.sender \in Process
        /\ m \notin recv[p]
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << pc, prop, est, decision, crashedCount, sent >>

ReceivePhase2(p, m) == 
  /\ \E m \in Message :
        /\ pc[p] = Wait2
        /\ m \in sent
        /\ m.type = "phase2"
        /\ m.sender \in Process
        /\ m \notin recv[p]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << pc, prop, view, est, decision, crashedCount, sent >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Process -> ControlLoc]
  /\ prop \in [Process -> Values]
  /\ view \in [Process -> [Process -> Values \cup {Bottom}]]
  /\ est \in [Process -> Values \cup {Bottom}]
  /\ decision \in [Process -> Values \cup {Bottom}]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Process -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Process :
    decision[p] # Bottom =>
      /\ decision[p] \in Values
      /\ \E q \in Process : prop[q] = decision[p]

Agreement ==
  \A p, q \in Process :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Assumptions
\* ----------------------------------------------------------------------
ASSUME 2 * T < N
ASSUME 0 <= F /\ F <= T
ASSUME N > 0
ASSUME Bottom \notin Values

====