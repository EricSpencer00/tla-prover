---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc    == 1 .. N
MsgType == {"p1", "p2"}
Phase   == {"b1", "w1", "b2", "w2", "choose", "done", "crashed"}

Value   == Values \cup {Bottom}

\* A message.  For phase‑1 messages the field `est` is ignored (set to Bottom).
Message == [type : MsgType,
            sender : Proc,
            value  : Value,
            est    : Value]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* N×N matrix of observed values
          prop,             \* proposed value of each process
          est,              \* estimated value after phase‑1
          dec,              \* decision value (Bottom if undecided)
          crashedCount,     \* number of crashed processes
          sent,             \* set of all messages that have been broadcast
          recv              \* messages received by each process

vars == << pc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} 
        THEN Bottom 
        ELSE CHOOSE v \in S : \A w \in S : w <= v

ReceivedFrom(p, t) == { m \in recv[p] : m.type = t }

ReceivedFromDistinct(p, t) == 
    { m.sender : m \in ReceivedFrom(p, t) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ prop \in [Proc -> Values]               \* each proposal is a value
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ LET m == [type |-> "p1",
                 sender |-> p,
                 value  |-> prop[p],
                 est    |-> Bottom]
       IN sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in sent
    /\ m.type = "p1"
    /\ m.sender \notin ReceivedFromDistinct(p, "p1")
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(ReceivedFromDistinct(p, "p1")) >= N - T
    /\ LET vals == { view[p][q] : q \in Proc } \cup { prop[p] }
       IN est' = [est EXCEPT ![p] = Max(vals)]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ LET m == [type |-> "p2",
                 sender |-> p,
                 value  |-> prop[p],
                 est    |-> est[p]]
       IN sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in sent
    /\ m.type = "p2"
    /\ m.sender \notin ReceivedFromDistinct(p, "p2")
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

DecideIfEnough(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Value :
          ( Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) >= N - T )
          /\ LET vChosen == v
             IN /\ dec' = [dec EXCEPT ![p] = vChosen]
                /\ pc'  = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoose(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality(ReceivedFromDistinct(p, "p2")) = N
    /\ \A v \in Value :
          ( Cardinality({ m \in recv[p] : m.type = "p2" /\ m.est = v }) < N - T )
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
    /\ pc[p] = "choose"
    /\ LET candidates == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }
       IN /\ candidates # {}
          /\ LET v == CHOOSE x \in candidates : TRUE
             IN /\ dec' = [dec EXCEPT ![p] = v]
                /\ pc'  = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p1 \in Proc :
        \/ BroadcastPhase1(p1)
        \/ BroadcastPhase2(p1)
        \/ Crash(p1)
    \/
    \E p2 \in Proc, m \in Message :
        \/ ReceivePhase1(p2, m)
        \/ ReceivePhase2(p2, m)
    \/
    \E p3 \in Proc :
        \/ ComputeEst(p3)
        \/ DecideIfEnough(p3)
        \/ MoveToChoose(p3)
        \/ ChooseAndDecide(p3)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> Phase]
    /\ view \in [Proc -> [Proc -> Value]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Value]
    /\ dec \in [Proc -> Value]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

====