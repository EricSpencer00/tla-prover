---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
PCValues == {"b1", "w1", "p", "b2", "w2", "done", "crashed", "choose"}

Message == [type : {"phase1", "phase2"},
            sender : 1..N,
            val    : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,          \* control location of each process
          view,        \* N x N matrix of observed values
          prop,        \* proposed value of each process
          est,         \* estimated value after phase 1
          dec,         \* decision value (Bottom if undecided)
          crashedCnt,  \* number of crashed processes
          sent,        \* set of all messages that have been broadcast
          recv         \* per‑process set of received messages

vars == << pc, view, prop, est, dec, crashedCnt, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxValue(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : v >= w

DistinctSenders(i, phase) ==
    { s \in 1..N : \E m \in recv[i] : m.type = phase /\ m.sender = s }

EstCount(i, v) ==
    Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v })

AllPhase2Senders(i) ==
    { s \in 1..N : \E m \in recv[i] : m.type = "phase2" /\ m.sender = s }

\* ----------------------------------------------------------------------
\* Initialisation
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in 1..N |-> "b1"]
    /\ prop = [i \in 1..N |-> CHOOSE v \in Values : TRUE]
    /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
    /\ est = [i \in 1..N |-> Bottom]
    /\ dec = [i \in 1..N |-> Bottom]
    /\ crashedCnt = 0
    /\ sent = {}
    /\ recv = [i \in 1..N |-> {}]

\* ----------------------------------------------------------------------
\* Phase 1 actions
\* ----------------------------------------------------------------------
Phase1Broadcast(i) ==
    /\ pc[i] = "b1"
    /\ LET m == [type |-> "phase1",
                sender |-> i,
                val    |-> prop[i],
                est    |-> Bottom] IN
       sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED << view, prop, est, dec, crashedCnt, recv >>

Phase1Receive(i) ==
    /\ pc[i] = "w1"
    /\ \E m \in sent :
         /\ m.type = "phase1"
         /\ ~(\E mm \in recv[i] : mm.sender = m.sender)  \* not yet received from this sender
         /\ LET view' == [view EXCEPT ![i][m.sender] = m.val] IN
            view' = view'  \* (assignment only for readability)
         /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCnt, sent >>

Phase1Compute(i) ==
    /\ pc[i] = "w1"
    /\ Cardinality(DistinctSenders(i, "phase1")) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxValue({ view[i][j] : j \in 1..N })]
    /\ pc' = [pc EXCEPT ![i] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedCnt, sent, recv >>

\* ----------------------------------------------------------------------
\* Phase 2 actions
\* ----------------------------------------------------------------------
Phase2Broadcast(i) ==
    /\ pc[i] = "b2"
    /\ LET m == [type |-> "phase2",
                sender |-> i,
                val    |-> prop[i],
                est    |-> est[i]] IN
       sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "w2"]
    /\ UNCHANGED << view, prop, est, dec, crashedCnt, recv >>

Phase2Receive(i) ==
    /\ pc[i] = "w2"
    /\ \E m \in sent :
         /\ m.type = "phase2"
         /\ ~(\E mm \in recv[i] : mm.sender = m.sender)  \* not yet received from this sender
         /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedCnt, sent >>

Phase2Decide(i) ==
    /\ pc[i] = "w2"
    /\ \E v \in Values :
         /\ EstCount(i, v) >= N - T
    /\ dec' = [dec EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCnt, sent, recv >>

Phase2Choose(i) ==
    /\ pc[i] = "w2"
    /\ Cardinality(AllPhase2Senders(i)) = N
    /\ \A v \in Values : EstCount(i, v) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, crashedCnt, sent, recv >>

ChooseDecision(i) ==
    /\ pc[i] = "choose"
    /\ LET candidates == { view[i][j] : j \in 1..N /\ view[i][j] # Bottom } IN
         candidates # {}
    /\ dec' = [dec EXCEPT ![i] = MaxValue(candidates)]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCnt, sent, recv >>

\* ----------------------------------------------------------------------
\* Crash action
\* ----------------------------------------------------------------------
Crash(i) ==
    /\ pc[i] # "crashed"
    /\ crashedCnt < F
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N : Phase1Broadcast(i)
    \/ \E i \in 1..N : Phase1Receive(i)
    \/ \E i \in 1..N : Phase1Compute(i)
    \/ \E i \in 1..N : Phase2Broadcast(i)
    \/ \E i \in 1..N : Phase2Receive(i)
    \/ \E i \in 1..N : Phase2Decide(i)
    \/ \E i \in 1..N : Phase2Choose(i)
    \/ \E i \in 1..N : ChooseDecision(i)
    \/ \E i \in 1..N : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [1..N -> PCValues]
    /\ view \in [1..N -> [1..N -> (Values \cup {Bottom})]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> (Values \cup {Bottom})]
    /\ dec \in [1..N -> (Values \cup {Bottom})]
    /\ crashedCnt \in Nat
    /\ sent \subseteq Message
    /\ recv \in [1..N -> SUBSET Message]

Validity ==
    \A i \in 1..N :
        /\ dec[i] # Bottom
        => /\ dec[i] \in Values
           /\ \E j \in 1..N : prop[j] = dec[i]

Agreement ==
    \A i, j \in 1..N :
        /\ dec[i] # Bottom /\ dec[j] # Bottom
        => dec[i] = dec[j]

====