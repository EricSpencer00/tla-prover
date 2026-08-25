---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

\*-----------------------------------------------------------------
\* CONSTANTS
\*-----------------------------------------------------------------
CONSTANTS N, T, F, Values, Bottom

\*-----------------------------------------------------------------
\* TYPE DEFINITIONS
\*-----------------------------------------------------------------
Proc == 1 .. N

Message == 
  [type : {"phase1", "phase2"},
   sender : Proc,
   value  : Values,
   est    : Values \cup {Bottom}]

\*-----------------------------------------------------------------
\* VARIABLES
\*-----------------------------------------------------------------
VARIABLES pc,          \* control location of each process
          view,        \* N x N matrix of observed values
          prop,        \* proposed value of each process
          est,         \* estimated value after phase 1
          dec,         \* decision value
          crashedCount,\* number of crashed processes
          sent,        \* set of all messages ever sent
          recv         \* messages received by each process

vars == << pc, view, prop, est, dec, crashedCount, sent, recv >>

\*-----------------------------------------------------------------
\* INITIAL STATE
\*-----------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "bcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\*-----------------------------------------------------------------
\* HELPERS
\*-----------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

DistinctSenders(ms) == { m.sender : m \in ms }

CountDistinctSenders(ms) == Cardinality(DistinctSenders(ms))

Phase1Msgs(p) == { m \in recv[p] : m.type = "phase1" }

Phase2Msgs(p) == { m \in recv[p] : m.type = "phase2" }

\*-----------------------------------------------------------------
\* ACTIONS
\*-----------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ pc[p] = "bcast1"
  /\ UNCHANGED << view, est, dec, crashedCount, recv >>
  /\ sent' = sent \cup { [type |-> "phase1",
                         sender |-> p,
                         value  |-> prop[p],
                         est    |-> Bottom] }
  /\ pc' = [pc EXCEPT ![p] = "wait1"]

ReceivePhase1(p, m) ==
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.sender # p
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

TransitionToPhase2(p) ==
  /\ pc[p] = "wait1"
  /\ CountDistinctSenders(Phase1Msgs(p)) >= N - T
  /\ let row == view[p] in
        est' = [est EXCEPT ![p] = Max({ row[q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
  /\ pc[p] = "bcast2"
  /\ UNCHANGED << view, est, dec, crashedCount, recv >>
  /\ sent' = sent \cup { [type |-> "phase2",
                         sender |-> p,
                         value  |-> prop[p],
                         est    |-> est[p]] }
  /\ pc' = [pc EXCEPT ![p] = "wait2"]

ReceivePhase2(p, m) ==
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m.sender # p
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

Decide(p, v) ==
  /\ pc[p] = "wait2"
  /\ v \in Values
  /\ CountDistinctSenders({ m \in Phase2Msgs(p) : m.est = v }) >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ CountDistinctSenders(Phase2Msgs(p)) = N
  /\ \A v \in Values :
        CountDistinctSenders({ m \in Phase2Msgs(p) : m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choose"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

Choose(p) ==
  /\ pc[p] = "choose"
  /\ let vals == { view[p][q] : q \in Proc } \ {Bottom} in
        vals # {}    \* there is at least one non‑bottom value
  /\ let chosen == Max(vals) in
        dec' = [dec EXCEPT ![p] = chosen] 
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\*-----------------------------------------------------------------
\* NEXT STATE RELATION
\*-----------------------------------------------------------------
Next ==
  \/ \E p \in Proc : BroadcastPhase1(p)
  \/ \E p \in Proc, m \in Message : ReceivePhase1(p, m)
  \/ \E p \in Proc : TransitionToPhase2(p)
  \/ \E p \in Proc : BroadcastPhase2(p)
  \/ \E p \in Proc, m \in Message : ReceivePhase2(p, m)
  \/ \E p \in Proc, v \in Values : Decide(p, v)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\*-----------------------------------------------------------------
\* SPECIFICATION
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* INVARIANTS
\*-----------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","done","crashed","choose"}]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est  \in [Proc -> (Values \cup {Bottom})]
  /\ dec  \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ crashedCount <= F
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

Validity ==
  \A p \in Proc :
    /\ dec[p] # Bottom => dec[p] \in Values
    /\ dec[p] # Bottom => \E q \in Proc : prop[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom /\ dec[q] # Bottom => dec[p] = dec[q]

\*-----------------------------------------------------------------
\* END MODULE
\*-----------------------------------------------------------------
====