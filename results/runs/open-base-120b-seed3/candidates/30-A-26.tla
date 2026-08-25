---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc,                \* control location of each process
          prop,              \* proposed value of each process
          view,              \* N×N matrix of observed values
          est,               \* estimated value after phase 1
          decision,          \* final decision value
          sent,              \* set of messages that have been broadcast
          recv               \* messages received by each process

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
ProcSet == 1..N

Msg == [type : {"phase1","phase2"},
        sender : ProcSet,
        val : Values,
        est  : Values \cup {Bottom}]

\* The set of processes that have crashed
Crashed == { i \in ProcSet : pc[i] = "crashed" }

\* ----------------------------------------------------------------------
\* Type constraints
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcSet -> {"bcast1","wait1","bcast2","wait2","choosing","done","crashed"}]
    /\ prop \in [ProcSet -> Values]
    /\ view \in [ProcSet -> [ProcSet -> Values \cup {Bottom}]]
    /\ est \in [ProcSet -> Values \cup {Bottom}]
    /\ decision \in [ProcSet -> Values \cup {Bottom}]
    /\ sent \subseteq Msg
    /\ recv \in [ProcSet -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in ProcSet |-> "bcast1"]
    /\ prop \in [ProcSet -> Values]           \* each process picks an arbitrary value
    /\ view = [i \in ProcSet |-> [j \in ProcSet |-> Bottom]]
    /\ est = [i \in ProcSet |-> Bottom]
    /\ decision = [i \in ProcSet |-> Bottom]
    /\ sent = {}
    /\ recv = [i \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ let m == [type |-> "phase1", sender |-> i, val |-> prop[i], est |-> Bottom] in
       sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ UNCHANGED <<prop, view, est, decision, recv>>

Receive1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ \A mm \in recv[i] : mm.sender # m.sender      \* not received yet from this sender
    /\ view' = [view EXCEPT ![i][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, sent>>

Transition1(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality({ j \in ProcSet : view[i][j] # Bottom }) >= N - T
    /\ LET maxVal == Max({ view[i][j] : j \in ProcSet })
       IN
       /\ est' = [est EXCEPT ![i] = maxVal]
       /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED <<prop, view, decision, sent, recv>>

Broadcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ let m == [type |-> "phase2", sender |-> i, val |-> prop[i], est |-> est[i]] in
       sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ UNCHANGED <<prop, view, est, decision, recv>>

Receive2(i, m) ==
    /\ pc[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ \A mm \in recv[i] : mm.sender # m.sender      \* not received yet from this sender
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<pc, prop, view, est, decision, sent>>

Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
          Cardinality({ m \in recv[i] :
                         m.type = "phase2" /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in Values :
                Cardinality({ m \in recv[i] :
                               m.type = "phase2" /\ m.est = w }) >= N - T
       IN
       /\ decision' = [decision EXCEPT ![i] = v]
       /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<prop, view, est, sent, recv>>

Choose(i) ==
    /\ pc[i] = "wait2"
    /\ \A v \in Values :
          Cardinality({ m \in recv[i] :
                         m.type = "phase2" /\ m.est = v }) < N - T
    /\ Cardinality({ j \in ProcSet : \E mm \in recv[i] : mm.sender = j }) = N
    /\ LET candidates == { view[i][j] : j \in ProcSet /\ view[i][j] # Bottom } IN
       /\ decision' = [decision EXCEPT ![i] = CHOOSE x \in candidates : TRUE]
       /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<prop, view, est, sent, recv>>

Crash(i) ==
    /\ pc[i] # "crashed"
    /\ Cardinality(Crashed) < F
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED <<prop, view, est, decision, sent, recv>>

\* ----------------------------------------------------------------------
\* The overall next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in ProcSet : Broadcast1(i)
    \/ \E i \in ProcSet, m \in Msg : Receive1(i, m)
    \/ \E i \in ProcSet : Transition1(i)
    \/ \E i \in ProcSet : Broadcast2(i)
    \/ \E i \in ProcSet, m \in Msg : Receive2(i, m)
    \/ \E i \in ProcSet : Decide(i)
    \/ \E i \in ProcSet : Choose(i)
    \/ \E i \in ProcSet : Crash(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<pc, prop, view, est, decision, sent, recv>>

Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Validity ==
    \A i \in ProcSet :
        decision[i] # Bottom => 
            /\ decision[i] \in Values
            /\ \E j \in ProcSet : prop[j] = decision[i]

Agreement ==
    \A i, j \in ProcSet :
        (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* ----------------------------------------------------------------------
\* Additional type constraints required by the description
\* ----------------------------------------------------------------------
Assumptions ==
    /\ N > 0
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T
    /\ Bottom \notin Values

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====