---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ---------- Constants (to be provided by the .cfg) ----------
CONSTANTS 
    N,          \* number of processes
    T,          \* maximum number of tolerated faults
    F,          \* actual number of faults (upper bound)
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special value not in Values

\* ---------- Derived sets ----------
Proc == 1..N
MsgType == {"Phase1", "Phase2"}

\* ---------- State variables ----------
VARIABLES 
    pc,                 \* control location per process
    proposal,           \* proposal value per process
    view,               \* N x N matrix of received values (initialized to Bottom)
    estimated,          \* estimated value per process (max of its view after Phase1)
    decision,           \* decision value per process (Bottom if undecided)
    crashedCount,       \* number of crashed processes
    sent,               \* set of messages that have been broadcast
    received            \* per-process set of messages that have been received

\* ---------- Message record ----------
Message == [type : MsgType,
            sender : Proc,
            prop : Values,
            est : VALUES \cup {Bottom}]

\* ---------- Helper definitions ----------
Max(set) == 
    IF set = {} THEN Bottom
    ELSE CHOOSE x \in set : 
            \A y \in set : y <= x

AllReceivedFromAll(view) == 
    \A i \in Proc : \A j \in Proc : view[i][j] # Bottom

\* ---------- Initial state ----------
Init ==
    /\ pc = [i \in Proc |-> "BroadcastPhase1"]
    /\ proposal = [i \in Proc |-> CHOOSE v \in Values : TRUE]  \* nondeterministic choice
    /\ view = [i \in Proc |-> [j \in Proc |-> Bottom]]
    /\ estimated = [i \in Proc |-> Bottom]
    /\ decision = [i \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [i \in Proc |-> {}]

\* ---------- Actions ----------
\* (1) Broadcast Phase1 message
BroadcastPhase1(i) ==
    /\ pc[i] = "BroadcastPhase1"
    /\ sent' = sent \cup {[type |-> "Phase1", sender |-> i,
                         prop |-> proposal[i], est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![i] = "WaitPhase1"]
    /\ UNCHANGED << proposal, view, estimated, decision,
                     crashedCount, received >>

\* (2) Receive a message (any type) while waiting for the corresponding phase
Receive(i, m) ==
    /\ pc[i] \in {"WaitPhase1", "WaitPhase2"}
    /\ m \in sent
    /\ (pc[i] = "WaitPhase1" => m.type = "Phase1")
    /\ (pc[i] = "WaitPhase2" => m.type = "Phase2")
    /\ view' = [view EXCEPT ![i][m.sender] = m.prop]
    /\ received' = [received EXCEPT ![i] = received[i] \cup {m}]
    /\ UNCHANGED << pc, proposal, estimated, decision,
                     crashedCount, sent >>

\* (3) After collecting enough Phase1 messages, compute estimated and move to Phase2 broadcast
ComputeEstAndBroadcastPhase2(i) ==
    /\ pc[i] = "WaitPhase1"
    /\ \E S \in SUBSET Proc :
         /\ Cardinality(S) >= N - T
         /\ \A j \in S : view[i][j] # Bottom
    /\ estimated' = [estimated EXCEPT ![i] = Max({ view[i][j] : j \in Proc })]
    /\ pc' = [pc EXCEPT ![i] = "BroadcastPhase2"]
    /\ UNCHANGED << proposal, view, decision, crashedCount, sent, received >>

\* (4) Broadcast Phase2 message
BroadcastPhase2(i) ==
    /\ pc[i] = "BroadcastPhase2"
    /\ sent' = sent \cup {[type |-> "Phase2", sender |-> i,
                         prop |-> proposal[i], est |-> estimated[i]}]
    /\ pc' = [pc EXCEPT ![i] = "WaitPhase2"]
    /\ UNCHANGED << proposal, view, estimated, decision,
                     crashedCount, received >>

\* (5) Decide when enough matching Phase2 messages are seen
DecideFromMatchingEst(i) ==
    /\ pc[i] = "WaitPhase2"
    /\ \E v \in Values :
         /\ Cardinality({ m \in received[i] : m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "Done"]
    /\ UNCHANGED << proposal, view, estimated, crashedCount, sent, received >>

\* (6) Move to choosing when all Phase2 messages received but no threshold met
MoveToChoosing(i) ==
    /\ pc[i] = "WaitPhase2"
    /\ \A j \in Proc : 
         \E m \in sent : m.sender = j /\ m.type = "Phase2"
    /\ \A v \in Values :
         Cardinality({ m \in received[i] : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ pc' = [pc EXCEPT ![i] = "Choosing"]
    /\ UNCHANGED << proposal, view, estimated, decision,
                     crashedCount, sent, received >>

\* (7) Deterministically choose a value from the local view and decide
ChooseAndDecide(i) ==
    /\ pc[i] = "Choosing"
    /\ \E v \in Values :
         /\ v \in { view[i][j] : j \in Proc }
    /\ decision' = [decision EXCEPT ![i] = v]
    /\ pc' = [pc EXCEPT ![i] = "Done"]
    /\ UNCHANGED << proposal, view, estimated, crashedCount, sent, received >>

\* (8) Crash a process (if fault budget not exceeded)
Crash(i) ==
    /\ pc[i] # "Crashed"
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![i] = "Crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << proposal, view, estimated, decision,
                     sent, received >>

\* ---------- Next-state relation ----------
Next ==
    \/ \E i \in Proc : BroadcastPhase1(i)
    \/ \E i \in Proc, m \in sent : Receive(i, m)
    \/ \E i \in Proc : ComputeEstAndBroadcastPhase2(i)
    \/ \E i \in Proc : BroadcastPhase2(i)
    \/ \E i \in Proc : DecideFromMatchingEst(i)
    \/ \E i \in Proc : MoveToChoosing(i)
    \/ \E i \in Proc : ChooseAndDecide(i)
    \/ \E i \in Proc : Crash(i)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<pc, proposal, view, estimated,
                         decision, crashedCount, sent, received>>

\* ---------- Type correctness ----------
TypeOK ==
    /\ pc \in [Proc -> {"BroadcastPhase1", "WaitPhase1",
                       "BroadcastPhase2", "WaitPhase2",
                       "Choosing", "Done", "Crashed"}]
    /\ proposal \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ estimated \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq [type : MsgType,
                      sender : Proc,
                      prop : Values,
                      est : (Values \cup {Bottom})]
    /\ received \in [Proc -> SUBSET sent]

\* ---------- Safety properties ----------
Validity ==
    \A i \in Proc :
        decision[i] # Bottom => decision[i] \in Values

Agreement ==
    \A i, j \in Proc :
        /\ decision[i] # Bottom
        /\ decision[j] # Bottom
        => decision[i] = decision[j]

\* ---------- Theorems (optional) ----------
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====