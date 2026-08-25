---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets and types
\* ----------------------------------------------------------------------
Proc == 1..N
Value == Values \cup {Bottom}
Message == [type   : {"Phase1", "Phase2"},
            sender : Proc,
            value  : Value,
            est    : Value]   \* for Phase1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N-by-N matrix of observed values
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          decision,         \* decided value (Bottom if not yet decided)
          crashedCount,     \* number of crashed processes
          sent,             \* set of all messages that have been sent
          recv              \* messages received by each process

vars == << pc, view, prop, est, decision, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S :
       \A w \in S : w <= v

ReceivedPhase1(p) ==
  { m \in sent : m.type = "Phase1" /\ m.sender \in recv[p] }

ReceivedPhase2(p) ==
  { m \in sent : m.type = "Phase2" /\ m.sender \in recv[p] }

EstCount(p, v) ==
  Cardinality({ m \in ReceivedPhase2(p) : m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "Broadcast1"]
  /\ prop \in [Proc -> Values]            \* each process proposes a value
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = "Broadcast1"
  /\ LET m == [type |-> "Phase1", sender |-> p,
               value |-> prop[p], est |-> Bottom] IN
     /\ sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "Wait1"]
  /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

ReceivePhase1(p) ==
  /\ pc[p] = "Wait1"
  /\ \E m \in sent :
        /\ m.type = "Phase1"
        /\ m.sender \notin { s \in Proc : \E mm \in recv[p] : mm = m } \* not yet received
        /\ view' = [view EXCEPT ![p][m.sender] = m.value]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << pc, prop, est, decision, crashedCount, sent >>
        
Phase1Ready(p) ==
  /\ pc[p] = "Wait1"
  /\ Cardinality(ReceivedPhase1(p)) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "Broadcast2"]
  /\ UNCHANGED << view, prop, decision, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
  /\ pc[p] = "Broadcast2"
  /\ LET m == [type |-> "Phase2", sender |-> p,
               value |-> prop[p], est |-> est[p]] IN
     /\ sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "Wait2"]
  /\ UNCHANGED << view, prop, est, decision, crashedCount, recv >>

ReceivePhase2(p) ==
  /\ pc[p] = "Wait2"
  /\ \E m \in sent :
        /\ m.type = "Phase2"
        /\ m.sender \notin { s \in Proc : \E mm \in recv[p] : mm = m }
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
        /\ UNCHANGED << pc, view, prop, est, decision, crashedCount, sent >>

Decide(p) ==
  /\ pc[p] = "Wait2"
  /\ \E v \in Value :
        /\ EstCount(p, v) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Choose(p) ==
  /\ pc[p] = "Wait2"
  /\ Cardinality(ReceivedPhase2(p)) = N
  /\ \A v \in Value : EstCount(p, v) < N - T
  /\ \E v \in { view[p][q] : q \in Proc /\ view[p][q] # Bottom } :
        decision' = [decision EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ crashedCount < F
  /\ pc[p] # "Crashed"
  /\ pc' = [pc EXCEPT ![p] = "Crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, decision, sent, recv >>

Next ==
  \/ \E p \in Proc : BroadcastPhase1(p)
  \/ \E p \in Proc : ReceivePhase1(p)
  \/ \E p \in Proc : Phase1Ready(p)
  \/ \E p \in Proc : BroadcastPhase2(p)
  \/ \E p \in Proc : ReceivePhase2(p)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"Broadcast1","Wait1","Broadcast2","Wait2",
                     "Done","Crashed","Choosing"}]
  /\ view \in [Proc -> [Proc -> Value]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Value]
  /\ decision \in [Proc -> Value]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    decision[p] # Bottom => \E q \in Proc : prop[q] = decision[p]

Agreement ==
  \A p, q \in Proc :
    (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====