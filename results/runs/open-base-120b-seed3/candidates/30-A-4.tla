---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets and helper functions
\* ----------------------------------------------------------------------
Proc == 1..N

Msg == [type : {"phase1", "phase2"},
        val  : Values,
        sender: Proc,
        est  : Values \cup {Bottom}]  \* est is used only for phase2

IsMax(v, S) == v \in S /\ \A w \in S : w <= v

MaxSet(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : IsMax(v, S)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc, view, prop, est, dec, crashedCount, sent, recv

\* pc[p] is the control location of process p
\* view[p][q] is the value p has recorded for q (Bottom initially)
\* prop[p] is the value proposed by p
\* est[p]  is the estimated value after phase 1 (Bottom initially)
\* dec[p]  is the decision value (Bottom if not decided)
\* crashedCount is the number of processes that have crashed so far
\* sent is the set of all messages that have been broadcast
\* recv[p] is the set of messages that p has received

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "b1"]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ prop \in [Proc -> Values]               \* each process picks a proposal
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
    /\ pc' = [pc EXCEPT ![p] = "w1"]
    /\ sent' = sent \cup { [type |-> "phase1",
                           val  |-> prop[p],
                           sender |-> p,
                           est   |-> Bottom] }
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase1(p, m) ==
    /\ m \in sent
    /\ m.type = "phase1"
    /\ pc[p] = "w1"
    /\ m.sender \notin { s \in Proc : \E mm \in recv[p] : mm.sender = s }
        \* ignore duplicate from same sender
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
    /\ pc[p] = "w1"
    /\ LET senders == { s \in Proc : \E m \in recv[p] : m.type = "phase1" /\ m.sender = s }
       IN Cardinality(senders) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxSet({ view[p][s] : s \in Proc })]
    /\ pc'  = [pc EXCEPT ![p] = "b2"]
    /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

BroadcastPhase2(p) ==
    /\ pc[p] = "b2"
    /\ pc' = [pc EXCEPT ![p] = "w2"]
    /\ sent' = sent \cup { [type |-> "phase2",
                           val  |-> prop[p],
                           sender |-> p,
                           est   |-> est[p]] }
    /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

ReceivePhase2(p, m) ==
    /\ m \in sent
    /\ m.type = "phase2"
    /\ pc[p] = "w2"
    /\ m.sender \notin { s \in Proc : \E mm \in recv[p] : mm.sender = s }
        \* ignore duplicate from same sender
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

DecideIfEnough(p) ==
    /\ pc[p] = "w2"
    /\ \E v \in Values :
         LET msgs == { m \in recv[p] : m.type = "phase2" /\ m.est = v }
         IN Cardinality(msgs) >= N - T
    /\ LET v == CHOOSE w \in Values :
                Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = w }) >= N - T
       IN /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc'  = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
    /\ pc[p] = "w2"
    /\ Cardinality({ m \in recv[p] : m.type = "phase2" }) = N
    /\ \A v \in Values :
         Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in Values :
         v # Bottom /\ \E s \in Proc : view[p][s] = v
    /\ LET v == CHOOSE w \in Values :
                w # Bottom /\ \E s \in Proc : view[p][s] = w
       IN /\ dec' = [dec EXCEPT ![p] = v]
          /\ pc'  = [pc EXCEPT ![p] = "done"]
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
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in Proc : DecideIfEnough(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< pc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"b1","w1","b2","w2","done","crashed","choose"}]
    /\ view \in [Proc -> [Proc -> Values]]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> Values \cup {Bottom}]
    /\ dec \in [Proc -> Values \cup {Bottom}]
    /\ crashedCount \in Nat
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

====