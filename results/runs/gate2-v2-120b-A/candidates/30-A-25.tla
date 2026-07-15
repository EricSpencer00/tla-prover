---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
ProcSet == 1..N
ValueSet == Values \cup {Bottom}
MessageTypes == {"Phase1", "Phase2"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    pc,          \* control location of each process
    view,        \* N-by-N matrix of observed values (each row is a process's view)
    propos,      \* each process's initially proposed value
    est,         \* each process's estimated value after Phase1
    decision,    \* each process's decided value (or Bottom)
    crashedCnt,  \* number of processes that have crashed
    sent,        \* set of all messages that have been broadcast
    rcvd         \* function: process -> set of messages it has received

\* ----------------------------------------------------------------------
\* Types (used in TypeOK)
\* ----------------------------------------------------------------------
PCStates == {"Broadcast1", "Wait1", "Broadcast2", "Wait2",
             "Done", "Crashed", "Choosing"}

Message == [type : {"Phase1", "Phase2"},
            sender : ProcSet,
            value : ValueSet,
            est : ValueSet]  \* 'est' is Bottom for Phase1 messages

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [p \in ProcSet |-> "Broadcast1"]
    /\ propos = [p \in ProcSet |-> CHOOSE v \in Values : TRUE]  \* nondeterministic proposal
    /\ view = [p \in ProcSet |-> [q \in ProcSet |-> Bottom]]
    /\ est = [p \in ProcSet |-> Bottom]
    /\ decision = [p \in ProcSet |-> Bottom]
    /\ crashedCnt = 0
    /\ sent = {}
    /\ rcvd = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxValue(vs) ==
    IF vs = {} THEN Bottom
    ELSE CHOOSE x \in vs : \A y \in vs : y <= x

ReceivedFrom(v, msgs) == { m \in msgs : m.sender = v }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Broadcast1(p) ==
    /\ pc[p] = "Broadcast1"
    /\ sent' = sent \cup { [type |-> "Phase1",
                           sender |-> p,
                           value |-> propos[p],
                           est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "Wait1"]
    /\ UNCHANGED <<view, propos, est, decision, crashedCnt, rcvd>>

Receive1(p) ==
    /\ pc[p] = "Wait1"
    /\ \E m \in sent :
          /\ m.type = "Phase1"
          /\ m.sender \notin ReceivedFrom(p, rcvd[p])
          /\ view' = [view EXCEPT ![p][m.sender] = m.value]
          /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<pc, propos, est, decision, crashedCnt, sent>>

TransitionToPhase2(p) ==
    /\ pc[p] = "Wait1"
    /\ Cardinality({ s \in ProcSet : view[p][s] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxValue({ view[p][s] : s \in ProcSet })]
    /\ pc' = [pc EXCEPT ![p] = "Broadcast2"]
    /\ UNCHANGED <<view, propos, decision, crashedCnt, sent, rcvd>>

Broadcast2(p) ==
    /\ pc[p] = "Broadcast2"
    /\ sent' = sent \cup { [type |-> "Phase2",
                           sender |-> p,
                           value |-> propos[p],
                           est |-> est[p]] }
    /\ pc' = [pc EXCEPT ![p] = "Wait2"]
    /\ UNCHANGED <<view, propos, est, decision, crashedCnt, rcvd>>

Receive2(p) ==
    /\ pc[p] = "Wait2"
    /\ \E m \in sent :
          /\ m.type = "Phase2"
          /\ m.sender \notin ReceivedFrom(p, rcvd[p])
          /\ view' = [view EXCEPT ![p][m.sender] = m.value]
          /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
    /\ UNCHANGED <<pc, propos, est, decision, crashedCnt, sent>>

DecideIfThreshold(p) ==
    /\ pc[p] = "Wait2"
    /\ \E v \in ValueSet :
          /\ Cardinality({ m \in rcvd[p] : m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ LET v == CHOOSE w \in ValueSet :
                Cardinality({ m \in rcvd[p] : m.type = "Phase2" /\ m.est = w }) >= N - T
       IN /\ decision' = [decision EXCEPT ![p] = v]
          /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<view, propos, est, crashedCnt, sent, rcvd>>

MoveToChoosing(p) ==
    /\ pc[p] = "Wait2"
    /\ \A v \in ValueSet :
          Cardinality({ m \in rcvd[p] : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ Cardinality({ m \in rcvd[p] : m.type = "Phase2" }) = N
    /\ pc' = [pc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<view, propos, est, decision, crashedCnt, sent, rcvd>>

ChooseAndDecide(p) ==
    /\ pc[p] = "Choosing"
    /\ LET candidates == { view[p][q] : q \in ProcSet /\ view[p][q] # Bottom } IN
       /\ candidates # {}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in candidates : TRUE]
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<view, propos, est, crashedCnt, sent, rcvd>>

Crash(p) ==
    /\ pc[p] # "Crashed"
    /\ pc[p] # "Done"
    /\ crashedCnt < F
    /\ pc' = [pc EXCEPT ![p] = "Crashed"]
    /\ crashedCnt' = crashedCnt + 1
    /\ UNCHANGED <<view, propos, est, decision, sent, rcvd>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in ProcSet : Broadcast1(p)
    \/ \E p \in ProcSet : Receive1(p)
    \/ \E p \in ProcSet : TransitionToPhase2(p)
    \/ \E p \in ProcSet : Broadcast2(p)
    \/ \E p \in ProcSet : Receive2(p)
    \/ \E p \in ProcSet : DecideIfThreshold(p)
    \/ \E p \in ProcSet : MoveToChoosing(p)
    \/ \E p \in ProcSet : ChooseAndDecide(p)
    \/ \E p \in ProcSet : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, view, propos, est, decision,
                     crashedCnt, sent, rcvd>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcSet -> PCStates]
    /\ propos \in [ProcSet -> Values]
    /\ view \in [ProcSet -> [ProcSet -> ValueSet]]
    /\ est \in [ProcSet -> ValueSet]
    /\ decision \in [ProcSet -> ValueSet]
    /\ crashedCnt \in Nat
    /\ sent \subseteq Message
    /\ rcvd \in [ProcSet -> SUBSET Message]

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
\* (Optional) Theorems asserting that the invariants are implied by Spec
\* (These are not required by the .cfg but help documentation)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====