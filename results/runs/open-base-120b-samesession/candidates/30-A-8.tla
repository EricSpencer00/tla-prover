---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Processes == 1..N
MessageTypes == {"p1", "p2"}

Message == [type : MessageTypes,
            sender : Processes,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location per process
          view,             \* local view matrix
          prop,             \* proposed value per process
          est,              \* estimated value per process
          dec,              \* decision value per process
          crashedCount,     \* number of crashed processes
          sent,             \* set of all messages that have been broadcast
          recv              \* messages received per process

vars == << pc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxVal(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : w <= v

DistinctSenders(p, typ) ==
  { m.sender : m \in recv[p] /\ m.type = typ }

CountDistinctSenders(p, typ) ==
  Cardinality( DistinctSenders(p, typ) )

Phase1Ready(p) ==
  CountDistinctSenders(p, "p1") >= N - T

Phase2Ready(p) ==
  \E v \in Values :
    Cardinality( { m.sender : m \in recv[p] /\ m.type = "p2" /\ m.est = v } ) >= N - T

AllPhase2Senders(p) ==
  Cardinality( DistinctSenders(p, "p2") ) = N

ValueSeenInView(p) ==
  { view[p][j] : j \in Processes } \ { Bottom }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Processes |-> "b1"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ prop \in [Processes -> Values]
  /\ est = [p \in Processes |-> Bottom]
  /\ dec = [p \in Processes |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Processes |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
  /\ pc[p] = "b1"
  /\ UNCHANGED << view, est, dec, crashedCount, recv >>
  /\ sent' = sent \cup {
        [type |-> "p1",
         sender |-> p,
         value  |-> prop[p],
         est    |-> Bottom]
      }
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED << prop >>

Receive1(p, m) ==
  /\ pc[p] = "w1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Phase1ToPhase2(p) ==
  /\ pc[p] = "w1"
  /\ Phase1Ready(p)
  /\ est' = [est EXCEPT ![p] = MaxVal( { view[p][j] : j \in Processes } )]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

Broadcast2(p) ==
  /\ pc[p] = "b2"
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>
  /\ sent' = sent \cup {
        [type |-> "p2",
         sender |-> p,
         value  |-> prop[p],
         est    |-> est[p]]
      }
  /\ pc' = [pc EXCEPT ![p] = "w2"]
    
Receive2(p, m) ==
  /\ pc[p] = "w2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

DecideFromPhase2(p) ==
  /\ pc[p] = "w2"
  /\ Phase2Ready(p)
  /\ \E v \in Values :
       Cardinality( { m.sender : m \in recv[p] /\ m.type = "p2" /\ m.est = v } ) >= N - T
  /\ LET v == CHOOSE w \in Values :
               Cardinality( { m.sender : m \in recv[p] /\ m.type = "p2" /\ m.est = w } ) >= N - T
     IN  /\ dec' = [dec EXCEPT ![p] = v]
         /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
  /\ pc[p] = "w2"
  /\ AllPhase2Senders(p)
  /\ ~Phase2Ready(p)
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

Choose(p) ==
  /\ pc[p] = "choosing"
  /\ ValueSeenInView(p) # {}
  /\ LET v == CHOOSE w \in Values : w \in ValueSeenInView(p)
     IN  /\ dec' = [dec EXCEPT ![p] = v]
         /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

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
  \/ \E p \in Processes : Broadcast1(p)
  \/ \E p \in Processes, m \in Message : Receive1(p, m)
  \/ \E p \in Processes : Phase1ToPhase2(p)
  \/ \E p \in Processes : Broadcast2(p)
  \/ \E p \in Processes, m \in Message : Receive2(p, m)
  \/ \E p \in Processes : DecideFromPhase2(p)
  \/ \E p \in Processes : MoveToChoosing(p)
  \/ \E p \in Processes : Choose(p)
  \/ \E p \in Processes : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Processes -> {"b1","w1","b2","w2","done","choosing","crashed"}]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ prop \in [Processes -> Values]
  /\ est \in [Processes -> (Values \cup {Bottom})]
  /\ dec \in [Processes -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Processes -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Processes :
    dec[p] # Bottom => \E q \in Processes : prop[q] = dec[p]

Agreement ==
  \A p, q \in Processes :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Validity /\ Agreement

====