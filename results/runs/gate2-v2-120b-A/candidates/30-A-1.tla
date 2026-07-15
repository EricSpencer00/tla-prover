---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ProcSet == 1..N

MessageType == {"phase1", "phase2"}

Message == [type : MessageType,
            sender : ProcSet,
            value  : Values,
            est    : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,          \* control location of each process
    localView,  \* N-by-N matrix of received values, indexed by (process, sender)
    prop,       \* proposed value of each process
    est,        \* estimated value after phase 1
    decision,   \* decided value (or Bottom if not yet decided)
    crashed,    \* set of crashed processes
    sent,       \* set of all messages that have been sent
    recv        \* set of messages that each process has received, indexed by process

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
Locs == {"bcast1", "wait1", "bcast2", "wait2", "choose", "done", "crashed"}

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcSet -> Locs]
    /\ localView \in [ProcSet -> [ProcSet -> (Values \cup {Bottom})]]
    /\ prop \in [ProcSet -> Values]
    /\ est \in [ProcSet -> (Values \cup {Bottom})]
    /\ decision \in [ProcSet -> (Values \cup {Bottom})]
    /\ crashed \subseteq ProcSet
    /\ sent \subseteq Message
    /\ recv \in [ProcSet -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in ProcSet |-> "bcast1"]
    /\ localView = [i \in ProcSet |-> [j \in ProcSet |-> Bottom]]
    /\ prop \in [ProcSet -> Values] \* each process chooses a value from Values
    /\ est = [i \in ProcSet |-> Bottom]
    /\ decision = [i \in ProcSet |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ recv = [i \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Action: Broadcast phase‑1 message
\* ----------------------------------------------------------------------
Bcast1(i) ==
    /\ pc[i] = "bcast1"
    /\ pc' = [pc EXCEPT ![i] = "wait1"]
    /\ sent' = sent \cup { [type |-> "phase1", sender |-> i, value |-> prop[i], est |-> Bottom] }
    /\ UNCHANGED <<localView, prop, est, decision, crashed, recv>>

\* ----------------------------------------------------------------------
\* Action: Receive a phase‑1 message
\* ----------------------------------------------------------------------
Recv1(i, m) ==
    /\ pc[i] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ m.sender \notin crashed
    /\ localView' = [localView EXCEPT ![i][m.sender] = m.value]
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashed, sent>>

\* ----------------------------------------------------------------------
\* Action: Transition after collecting enough phase‑1 messages
\* ----------------------------------------------------------------------
AfterPhase1(i) ==
    /\ pc[i] = "wait1"
    /\ Cardinality({ m \in recv[i] : m.type = "phase1" }) >= N - T
    /\ est' = [est EXCEPT ![i] = 
                IF est[i] = Bottom THEN 
                    Max({ localView[i][j] : j \in ProcSet })
                ELSE est[i]]
    /\ pc' = [pc EXCEPT ![i] = "bcast2"]
    /\ UNCHANGED <<localView, prop, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: Broadcast phase‑2 message
\* ----------------------------------------------------------------------
Bcast2(i) ==
    /\ pc[i] = "bcast2"
    /\ pc' = [pc EXCEPT ![i] = "wait2"]
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> i,
                           value |-> prop[i],
                           est   |-> est[i]] }
    /\ UNCHANGED <<localView, prop, est, decision, crashed, recv>>

\* ----------------------------------------------------------------------
\* Action: Receive a phase‑2 message
\* ----------------------------------------------------------------------
Recv2(i, m) ==
    /\ pc[i] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ m.sender \notin crashed
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
    /\ UNCHANGED <<pc, localView, prop, est, decision, crashed, sent>>

\* ----------------------------------------------------------------------
\* Action: Decide after enough matching phase‑2 messages
\* ----------------------------------------------------------------------
Decide(i) ==
    /\ pc[i] = "wait2"
    /\ \E v \in Values :
          Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, prop, est, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: Move to choosing state when all phase‑2 messages received
\* ----------------------------------------------------------------------
MoveToChoose(i) ==
    /\ pc[i] = "wait2"
    /\ Cardinality({ m \in recv[i] : m.type = "phase2" }) = N
    /\ \A v \in Values :
          Cardinality({ m \in recv[i] : m.type = "phase2" /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED <<localView, prop, est, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: Deterministic choosing (pick the maximum seen value)
\* ----------------------------------------------------------------------
Choose(i) ==
    /\ pc[i] = "choose"
    /\ decision' = [decision EXCEPT ![i] = 
                     Max({ localView[i][j] : j \in ProcSet })]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<localView, prop, est, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Action: Crash a process
\* ----------------------------------------------------------------------
Crash(i) ==
    /\ i \in ProcSet \ crashed
    /\ Cardinality(crashed) < F
    /\ crashed' = crashed \cup {i}
    /\ pc' = [pc EXCEPT ![i] = "crashed"]
    /\ UNCHANGED <<localView, prop, est, decision, sent, recv>>

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED <<pc, localView, prop, est, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in ProcSet : Bcast1(i)
    \/ \E i \in ProcSet, m \in sent : Recv1(i, m)
    \/ \E i \in ProcSet : AfterPhase1(i)
    \/ \E i \in ProcSet : Bcast2(i)
    \/ \E i \in ProcSet, m \in sent : Recv2(i, m)
    \/ \E i \in ProcSet : Decide(i)
    \/ \E i \in ProcSet : MoveToChoose(i)
    \/ \E i \in ProcSet : Choose(i)
    \/ \E i \in ProcSet : Crash(i)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, localView, prop, est, decision, crashed, sent, recv>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A i \in ProcSet :
        IF decision[i] # Bottom THEN decision[i] \in Values

Agreement ==
    \A i, j \in ProcSet :
        (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====