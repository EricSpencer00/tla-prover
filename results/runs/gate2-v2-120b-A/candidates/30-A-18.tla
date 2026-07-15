---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ProcSet == 1..N

\* ----------------------------------------------------------------------
\* Message type definition
\* ----------------------------------------------------------------------
Message == 
    [type : {"phase1", "phase2"},
     sender : ProcSet,
     value : Values,
     est : Values \cup {Bottom}]

Phase1Msg(v) == [type |-> "phase1",  sender |-> ?, value |-> v, est |-> Bottom]
Phase2Msg(v, e) == [type |-> "phase2", sender |-> ?, value |-> v, est |-> e]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,            \* control location per process
    proposal,      \* each process's initial proposal (immutable)
    view,          \* N-by-N matrix of received values, initially Bottom
    est,           \* per-process estimated value after phase 1
    decision,      \* per-process decision value, initially Bottom
    crashed,       \* set of crashed processes
    sent,          \* set of messages that have been broadcast
    rcvd           \* per-process set of messages received

\* ----------------------------------------------------------------------
\* Control locations (enumerated as strings)
\* ----------------------------------------------------------------------
pcVals == {"bcast1", "wait1", "broadcast2", "wait2", 
           "choose", "done", "crash"}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcSet -> pcVals]
    /\ proposal \in [ProcSet -> Values]
    /\ view \in [ProcSet -> [ProcSet -> Values]]
    /\ est \in [ProcSet -> Values \cup {Bottom}]
    /\ decision \in [ProcSet -> Values \cup {Bottom}]
    /\ crashed \in SUBSET ProcSet
    /\ sent \subseteq Message
    /\ rcvd \in [ProcSet -> SUBSET Message]
    /\ \A p \in ProcSet:
         /\ pc[p] = "crash" => p \in crashed
         /\ p \in crashed => pc[p] = "crash"

\* maximum function over a set that may contain Bottom
Max(s) ==
    IF s = {} THEN Bottom
    ELSE
      LET nonBot == s \ {Bottom} IN
        IF nonBot = {} THEN Bottom
        ELSE CHOOSE x \in nonBot : \A y \in nonBot : y <= x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in ProcSet |-> "bcast1"]
    /\ proposal \in [p \in ProcSet |-> Values] \* nondeterministic assignment
    /\ view = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ est = [p \in ProcSet |-> Bottom]
    /\ decision = [p \in ProcSet |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ rcvd = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ pc[p] = "bcast1"
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ sent' = sent \cup { [type |-> "phase1",
                            sender |-> p,
                            value |-> proposal[p],
                            est |-> Bottom] }
    /\ UNCHANGED <<proposal, view, est, decision, crashed, rcvd>>

ReceivePhase1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
         /\ m.type = "phase1"
         /\ m.sender \notin crashed
         /\ view[p][m.sender] = Bottom
         /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<pc, proposal, est, decision, crashed, sent>>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ q \in ProcSet : view[p][q] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max(Range(view[p]))]
    /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<proposal, view, decision, crashed, sent, rcvd>>

BroadcastPhase2(p) ==
    /\ pc[p] = "broadcast2"
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ sent' = sent \cup { [type |-> "phase2",
                            sender |-> p,
                            value |-> proposal[p],
                            est |-> est[p]] }
    /\ UNCHANGED <<proposal, view, est, decision, crashed, rcvd>>

ReceivePhase2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
         /\ m.type = "phase2"
         /\ m.sender \notin crashed
         /\ view[p][m.sender] = Bottom
         /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<pc, proposal, est, decision, crashed, sent>>

DecideFromEst(p) ==
    /\ pc[p] = "wait2"
    /\ \E e \in Values :
         /\ Cardinality({ m \in rcvd[p] : m.type = "phase2" /\ m.est = e }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = e]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposal, view, est, crashed, sent, rcvd>>

MoveToChoose(p) ==
    /\ pc[p] = "wait2"
    /\ ~(\E e \in Values :
            Cardinality({ m \in rcvd[p] : m.type = "phase2" /\ m.est = e }) >= N - T)
    /\ Cardinality({ m \in rcvd[p] : m.type = "phase2" }) = N
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<proposal, view, est, decision, crashed, sent, rcvd>>

Choose(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in Values :
         /\ v \in Range(view[p])
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<proposal, view, est, crashed, sent, rcvd>>

Crash(p) ==
    /\ p \notin crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {p}
    /\ pc' = [pc EXCEPT ![p] = "crash"]
    /\ UNCHANGED <<proposal, view, est, decision, sent, rcvd>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet : BroadcastPhase1(p)
    \/ \E p \in ProcSet : ReceivePhase1(p)
    \/ \E p \in ProcSet : ComputeEst(p)
    \/ \E p \in ProcSet : BroadcastPhase2(p)
    \/ \E p \in ProcSet : ReceivePhase2(p)
    \/ \E p \in ProcSet : DecideFromEst(p)
    \/ \E p \in ProcSet : MoveToChoose(p)
    \/ \E p \in ProcSet : Choose(p)
    \/ \E p \in ProcSet : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, proposal, view, est, decision, crashed, sent, rcvd>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A p \in ProcSet :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in ProcSet :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Liveness properties (optional, not required by the .cfg)
\* ----------------------------------------------------------------------
Termination ==
    \A p \in ProcSet : p \in crashed \/ pc[p] = "done"

ConditionalTermination ==
    /\ \E p \in ProcSet : proposal[p] = Max(Values)
    /\ \A p \in ProcSet : p \in crashed \/ pc[p] = "done"

=============================================================================