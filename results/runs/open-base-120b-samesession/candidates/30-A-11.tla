---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Basic sets and derived constants
\* ----------------------------------------------------------------------
Proc == 1 .. N

Phase1 == "phase1"
Phase2 == "phase2"

Locs == {"bcast1", "wait1", "bcast2", "wait2",
         "choosing", "done", "crashed"}

Msg == [type : {"phase1","phase2"},
        sender : Proc,
        prop   : Values,
        est    : Values]   \* for phase1 messages est = Bottom

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,                \* control location of each process
          prop,              \* proposed value of each process
          view,              \* N->N matrix of received proposals (or Bottom)
          est,               \* estimated value after phase 1
          decision,          \* decided value (Bottom if undecided)
          crashedCount,      \* number of crashed processes
          sent,              \* set of messages that have been broadcast
          recv               \* mapping: process -> set of messages it has received

vars == << pc, prop, view, est, decision,
          crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum of a non‑empty set of values (Values are totally ordered)
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S :
        \A y \in S : y <= x

\* Number of distinct senders from which p has a non‑Bottom entry in its view
DistinctSenders(p) ==
  { s \in Proc : view[p][s] # Bottom }

\* Set of estimated values seen by p in phase‑2 messages it has received
RecEst(p) ==
  { m.est : m \in recv[p] /\ m.type = "phase2" }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "bcast1"]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]   \* arbitrary proposal
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ decision = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Broadcast a phase‑1 message
Broadcast1(p) ==
  /\ pc[p] = "bcast1"
  /\ let m == [type |-> "phase1",
               sender |-> p,
               prop |-> prop[p],
               est |-> Bottom] 
     in sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << prop, view, est, decision,
                 crashedCount, recv >>

\* Receive a phase‑1 message
Receive1(p, m) ==
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, decision,
                 crashedCount, sent >>

\* After having enough phase‑1 messages, compute estimate and go to phase‑2 broadcast
ComputeEst(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality(DistinctSenders(p)) >= N - T
  /\ let vals == { view[p][s] : s \in Proc /\ view[p][s] # Bottom } in
       est' = [est EXCEPT ![p] = Max(vals)]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << prop, view, decision,
                 crashedCount, sent, recv >>

\* Broadcast a phase‑2 message
Broadcast2(p) ==
  /\ pc[p] = "bcast2"
  /\ let m == [type |-> "phase2",
               sender |-> p,
               prop |-> prop[p],
               est |-> est[p]] 
     in sent' = sent \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << prop, view, est, decision,
                 crashedCount, recv >>

\* Receive a phase‑2 message
Receive2(p, m) ==
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, decision,
                 crashedCount, sent >>

\* Decide when N‑T equal estimated values have been seen
DecideFromEst(p) ==
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        Cardinality({ m \in recv[p] :
                     m.type = "phase2" /\ m.est = v }) >= N - T
  /\ LET v == CHOOSE w \in Values :
                 Cardinality({ m \in recv[p] :
                               m.type = "phase2" /\ m.est = w }) >= N - T
     IN  decision' = [decision EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

\* Move to choosing state when all phase‑2 messages have been received
MoveToChoosing(p) ==
  /\ pc[p] = "wait2"
  /\ Cardinality({ m \in recv[p] : m.type = "phase2" }) = N
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] :
                     m.type = "phase2" /\ m.est = v }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << prop, view, est, decision,
                 crashedCount, sent, recv >>

\* Deterministically choose a value appearing in the local view and decide
Choose(p) ==
  /\ pc[p] = "choosing"
  /\ LET vals == { view[p][s] : s \in Proc /\ view[p][s] # Bottom } IN
        vals # {}   \* there is at least one value
  /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in vals : TRUE]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << prop, view, est, crashedCount, sent, recv >>

\* Crash a process (if fewer than F have crashed so far)
Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << prop, view, est, decision,
                 sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ Broadcast1(p)
    \/ \E m \in sent : Receive1(p, m)
    \/ ComputeEst(p)
    \/ Broadcast2(p)
    \/ \E m \in sent : Receive2(p, m)
    \/ DecideFromEst(p)
    \/ MoveToChoosing(p)
    \/ Choose(p)
    \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> Locs]
  /\ prop \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ decision \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ crashedCount <= F
  /\ sent \subseteq Msg
  /\ recv \in [Proc -> SUBSET Msg]
  /\ \A p \in Proc :
        \A m \in recv[p] :
          m \in sent
  /\ \A p \in Proc :
        view[p][p] = prop[p]   \* a process always knows its own proposal

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    decision[p] # Bottom => decision[p] \in { prop[q] : q \in Proc }

Agreement ==
  \A p,q \in Proc :
    /\ decision[p] # Bottom
    /\ decision[q] # Bottom
    => decision[p] = decision[q]

====