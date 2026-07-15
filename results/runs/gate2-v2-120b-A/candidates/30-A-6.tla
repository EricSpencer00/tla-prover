----------------------------- MODULE cbc_max -----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    N,          \* Number of processes
    T,          \* Max tolerated crash faults
    F,          \* Upper bound on actual crashes
    Values,     \* Finite set of possible proposal values
    Bottom      \* Special bottom value not in Values

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
Proc == 1..N
MsgTypes == {"phase1", "phase2"}
\* Message record
Msg == [type : MsgTypes,
        sender : Proc,
        propVal : Values \cup {Bottom},
        estVal  : Values \cup {Bottom}]  \* estVal is Bottom for phase1 msgs

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,            \* control location of each process
    localView,    \* N x N matrix of observed values (proc -> sender -> value)
    propVal,      \* each process's proposed value
    estVal,       \* each process's estimated value
    decision,    \* each process's decision value (or Bottom)
    crashedCount, \* number of crashed processes
    sent,         \* set of sent messages
    received      \* msgs received by each process (proc -> set of Msg)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK == 
    /\ pc \in [Proc -> {"bcast1", "wait1", "bcast2", "wait2", "choose", "done", "crashed"}]
    /\ localView \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ propVal \in [Proc -> (Values \cup {Bottom})]
    /\ estVal \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ sent \subseteq Msg
    /\ received \in [Proc -> SUBSET Msg]
    /\ crashedCount <= F
    /\ \A p \in Proc: pc[p] = "crashed" => decision[p] = Bottom

\* Maximum of a set, returning Bottom if the set is empty
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Count of messages with a given estimated value received by p
CountEst(p, v) ==
    Cardinality({ m \in received[p] :
                    m.type = "phase2" /\ m.estVal = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ localView = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ propVal = [p \in Proc |-> Bottom]   \* will be set nondeterministically
    /\ estVal = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]
    /\ \A p \in Proc: propVal[p] \in Values

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BcastPhase1(p) ==
    /\ pc[p] = "bcast1"
    /\ LET m == [type |-> "phase1",
                 sender |-> p,
                 propVal |-> propVal[p],
                 estVal |-> Bottom] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<localView, propVal, estVal, decision,
                    crashedCount, received>>

RecvPhase1(p, m) ==
    /\ pc[p] = "wait1"
    /\ m \in sent
    /\ m.type = "phase1"
    /\ localView' = [localView EXCEPT ![p][m.sender] = m.propVal]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, estVal, decision,
                    crashedCount, sent>>

StartPhase2(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ q \in Proc : localView[p][q] # Bottom }) >= N - T
    /\ estVal' = [estVal EXCEPT ![p] = Max({ localView[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<localView, propVal, decision,
                    crashedCount, sent, received>>

BcastPhase2(p) ==
    /\ pc[p] = "bcast2"
    /\ LET m == [type |-> "phase2",
                 sender |-> p,
                 propVal |-> propVal[p],
                 estVal |-> estVal[p]] IN
       /\ sent' = sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<localView, propVal, estVal, decision,
                    crashedCount, received>>

RecvPhase2(p, m) ==
    /\ pc[p] \in {"wait2", "choose", "wait1"}
    /\ m \in sent
    /\ m.type = "phase2"
    /\ localView' = [localView EXCEPT ![p][m.sender] = m.propVal]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, propVal, estVal, decision,
                    crashedCount, sent>>

DecideFromEst(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          /\ CountEst(p, v) >= N - T
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, propVal, estVal,
                    crashedCount, sent, received>>

MoveToChoose(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ q \in Proc : localView[p][q] # Bottom }) = N
    /\ pc' = [pc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<localView, propVal, estVal,
                    decision, crashedCount, sent, received>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choose"
    /\ \E v \in Values :
          /\ v \in { localView[p][q] : q \in Proc }
          /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<localView, propVal, estVal,
                    crashedCount, sent, received>>

Crash(p) ==
    /\ crashedCount < F
    /\ pc[p] # "crashed"
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<localView, propVal, estVal,
                    decision, sent, received>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : BcastPhase1(p)
    \/ \E p \in Proc, m \in sent : RecvPhase1(p, m)
    \/ \E p \in Proc : StartPhase2(p)
    \/ \E p \in Proc : BcastPhase2(p)
    \/ \E p \in Proc, m \in sent : RecvPhase2(p, m)
    \/ \E p \in Proc : DecideFromEst(p)
    \/ \E p \in Proc : MoveToChoose(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, localView, propVal, estVal,
                    decision, crashedCount, sent, received>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Liveness property (optional for completeness)
\* ----------------------------------------------------------------------
Termination ==
    \A p \in Proc : pc[p] \in {"done", "crashed"}

=============================================================================