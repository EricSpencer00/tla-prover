---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

\* Message definition
Message == [type   : {"ph1", "ph2"},
            val    : Values,
            sender : Proc,
            est    : Values]   \* for phase‑1 messages est = Bottom

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* control location of each process
          view,             \* [p \in Proc |-> [q \in Proc |-> Values]]
          prop,             \* proposed value of each process
          est,              \* estimated value after phase 1
          decision,         \* decided value (Bottom if not yet decided)
          crashedCount,     \* number of crashed processes
          sent,             \* set of all messages that have been broadcast
          recv              \* [p \in Proc |-> SUBSET Message]

vars == << pc, view, prop, est, decision,
           crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum of a non‑empty set of values (according to the total order on Values)
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

\* The set of values that a process p has learned (its view, ignoring Bottom)
LearnedVals(p) == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

\* Number of distinct senders from which p has received a phase‑1 message
RecvPhase1Senders(p) ==
    { m.sender : m \in recv[p] /\ m.type = "ph1" }

\* Number of distinct senders from which p has received a phase‑2 message
RecvPhase2Senders(p) ==
    { m.sender : m \in recv[p] /\ m.type = "ph2" }

\* Count of phase‑2 messages with estimated value v received by p
CountEst(p, v) ==
    Cardinality({ m \in recv[p] : m.type = "ph2" /\ m.est = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]                      \* broadcast phase‑1
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]                     \* each process proposes a value
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Broadcast phase‑1 message
BroadcastPhase1(p) ==
    /\ pc[p] = "b1"
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ sent' = sent \cup { [type |-> "ph1",
                           val  |-> prop[p],
                           sender|-> p,
                           est  |-> Bottom] }
    /\ UNCHANGED << view, prop, est, decision,
                    crashedCount, recv >>

\* (2) Receive a phase‑1 message
ReceivePhase1(p, m) ==
    /\ pc[p] = "w1"
    /\ m \in sent
    /\ m.type = "ph1"
    /\ view[p][m.sender] = Bottom               \* first time we learn from sender
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision,
                    crashedCount, sent >>

\* (3) After receiving enough phase‑1 messages, compute estimate and broadcast phase‑2
ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ Cardinality(RecvPhase1Senders(p)) >= N - T
    /\ est' = [est EXCEPT ![p] = Max(LearnedVals(p))]
    /\ pc' = [pc EXCEPT ![p] = "b2"]
    /\ sent' = sent \cup { [type |-> "ph2",
                           val  |-> prop[p],
                           sender|-> p,
                           est  |-> est'[p]] }
    /\ UNCHANGED << view, prop, decision,
                    crashedCount, recv >>

\* (4) Broadcast phase‑2 message (already performed in ComputeEst)

\* (5) Receive a phase‑2 message
ReceivePhase2(p, m) ==
    /\ pc[p] = "w2"
    /\ m \in sent
    /\ m.type = "ph2"
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, decision,
                    crashedCount, sent >>

\* (6) Decide when a value appears in at least N‑T phase‑2 messages
Decide(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
          CountEst(p, v) >= N - T
    /\ LET v == CHOOSE w \in Values : CountEst(p, w) >= N - T IN
       /\ decision' = [decision EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est,
                    crashedCount, sent, recv >>

\* (7) If all N phase‑2 messages received without reaching the threshold, move to choosing
MoveToChoose(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality(RecvPhase2Senders(p)) = N
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED << view, prop, est, decision,
                    crashedCount, sent, recv >>

\* (8) Choose deterministically a value that appears in the local view
Choose(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in LearnedVals(p) : TRUE
    /\ LET v == CHOOSE w \in LearnedVals(p) : TRUE IN
       /\ decision' = [decision EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est,
                    crashedCount, sent, recv >>

\* (9) Crash a process (allowed while fewer than F have crashed)
Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << view, prop, est, decision,
                    sent, recv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoose(p)
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
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choose"}]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values]
    /\ decision \in [Proc -> Values]
    /\ crashedCount \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        /\ pc[p] = "done"
        => decision[p] \in { prop[q] : q \in Proc }

Agreement ==
    \A p, q \in Proc :
        /\ pc[p] = "done"
        /\ pc[q] = "done"
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Theorem statements (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====