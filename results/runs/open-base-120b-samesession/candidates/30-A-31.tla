---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Process set
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition
Message == [type : {"p1","p2"},
            sender : Proc,
            value  : Values,
            est    : Values]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES pc,        \* control location of each process
          view,      \* local view matrix (proc × proc) of values
          prop,      \* proposed value of each process
          est,       \* estimated value after phase 1
          dec,       \* decision value of each process
          crashed,   \* set of crashed processes
          sent,      \* set of messages that have been broadcast
          recv       \* messages received by each process

vars == << pc, view, prop, est, dec, crashed, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(p, typ) ==
  { m.sender : m \in recv[p] /\ m.type = typ }

Phase1Send(p) ==
  [type |-> "p1", sender |-> p, value |-> prop[p], est |-> Bottom]

Phase2Send(p) ==
  [type |-> "p2", sender |-> p, value |-> prop[p], est |-> est[p]]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashed = {}
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions

BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ let m == Phase1Send(p) in
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![p] = "w1"]
       /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ let m == Phase2Send(p) in
       /\ sent' = sent \cup {m}
       /\ pc'   = [pc EXCEPT ![p] = "w2"]
       /\ UNCHANGED <<view, prop, est, dec, crashed, recv>>

Receive(p, m) ==
  /\ p \notin crashed
  /\ m \in sent
  /\ m \notin recv[p]
  /\ ( (pc[p] = "w1" /\ m.type = "p1") \/
       (pc[p] = "w2" /\ m.type = "p2") )
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = IF m.type = "p1"
               THEN [view EXCEPT ![p][m.sender] = m.value]
               ELSE [view EXCEPT ![p][m.sender] = m.est]
  /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality(ReceivedFrom(p, "p1")) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ pc'  = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

Decide(p) ==
  /\ pc[p] = "w2"
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T
  /\ LET v == CHOOSE { v \in Values :
                         Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T } IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

ChooseState(p) ==
  /\ pc[p] = "w2"
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) < N - T
  /\ \A s \in Proc :
        \E m \in recv[p] : m.type = "p2" /\ m.sender = s
  /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } IN
       /\ candidates # {}
  /\ LET v == Max(candidates) IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ pc'  = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Crash(p) ==
  /\ p \notin crashed
  /\ Cardinality(crashed) < F
  /\ crashed' = crashed \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "crash"]
  /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in Message : Receive(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : ChooseState(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
  /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crash","choose"}]
  /\ view \in [Proc -> [Proc -> Values]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values]
  /\ dec \in [Proc -> Values]
  /\ crashed \subseteq Proc
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties

Validity ==
  \A p \in Proc :
    dec[p] # Bottom => dec[p] \in { prop[q] : q \in Proc }

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

\* ----------------------------------------------------------------------
\* The required identifiers
SPECIFICATION == Spec
INVARIANTS == TypeOK, Validity, Agreement

====