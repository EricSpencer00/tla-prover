---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,          \* number of processes
    T,          \* tolerated faults
    F,          \* actual faults (upper bound)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special bottom value not in Values

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc      == 1 .. N
Message   == [type : {"phase1","phase2"},
              sender : Proc,
              val   : Values,
              est   : Values]   \* for phase1 messages, est = Bottom

ValueSet  == Values \cup {Bottom}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,          \* [p \in Proc -> {"bcast1","wait1","bcast2","wait2","choosing","done","crashed"}]
    view,        \* [p \in Proc -> [q \in Proc -> ValueSet]]
    propose,     \* [p \in Proc -> Values]
    est,         \* [p \in Proc -> ValueSet]
    decision,    \* [p \in Proc -> ValueSet]
    crashedCnt,  \* Nat
    sent,        \* SUBSET Message
    recv         \* [p \in Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxVals(S) == 
    IF S = {} THEN Bottom
    ELSE CHOOSE v \in S : \A w \in S : w <= v

\* Set of distinct senders of phase‑1 messages received by p
SendersPhase1(p) == { m.sender : m \in recv[p] /\ m.type = "phase1" }

\* Set of distinct senders of phase‑2 messages received by p
SendersPhase2(p) == { m.sender : m \in recv[p] /\ m.type = "phase2" }

\* Count of phase‑2 messages with estimated value v received by p
CountEst(p, v) == Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = v })

\* Values appearing in p's view (excluding Bottom)
ValsInView(p) == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ propose \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCnt = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "bcast1"
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           val   |-> propose[p],
                           est   |-> Bottom] }
    /\ UNCHANGED <<view, propose, est, decision, crashedCnt, recv>>

ReceivePhase1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propose, est, decision, crashedCnt, sent>>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(SendersPhase1(p)) >= N - T
    /\ let vals == { view[p][q] : q \in Proc /\ view[p][q] # Bottom } in
       est' = [est EXCEPT ![p] = MaxVals(vals)]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<view, propose, decision, crashedCnt, sent, recv>>

BroadcastPhase2(p) ==
    /\ pc[p] = "bcast2"
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> p,
                           val   |-> propose[p],
                           est   |-> est[p]] }
    /\ UNCHANGED <<view, propose, est, decision, crashedCnt, recv>>

ReceivePhase2(p, m) ==
    /\ pc[p] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<pc, propose, est, decision, crashedCnt, sent>>

DecideIfEnough(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
         CountEst(p, v) >= N - T
    /\ LET v == CHOOSE v \in Values : CountEst(p, v) >= N - T IN
          decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, est, crashedCnt, sent, recv>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ \A v \in Values : CountEst(p, v) < N - T
    /\ Cardinality(SendersPhase2(p)) = N
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, propose, est, decision, crashedCnt, sent, recv>>

Choosing(p) ==
    /\ pc[p] = "choosing"
    /\ ValsInView(p) # {}
    /\ LET v == CHOOSE ValsInView(p) IN
          decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, est, crashedCnt, sent, recv>>

Crash(p) ==
    /\ crashedCnt < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<view, propose, est, decision, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ BroadcastPhase1(p)
        \/ \E m \in Message : ReceivePhase1(p, m)
        \/ ComputeEst(p)
        \/ BroadcastPhase2(p)
        \/ \E m \in Message : ReceivePhase2(p, m)
        \/ DecideIfEnough(p)
        \/ MoveToChoosing(p)
        \/ Choosing(p)
        \/ Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, view, propose, est, decision, crashedCnt, sent, recv>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","choosing","done","crashed"}]
    /\ view \in [Proc -> [Proc -> ValueSet]]
    /\ propose \in [Proc -> Values]
    /\ est \in [Proc -> ValueSet]
    /\ decision \in [Proc -> ValueSet]
    /\ crashedCnt \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom =>
            /\ decision[p] \in Values
            /\ \E q \in Proc : decision[p] = propose[q]

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

====