---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N            \* number of processes
CONSTANT T            \* maximum number of faulty processes tolerated
CONSTANT F            \* actual number of crash failures allowed
CONSTANT Values       \* finite set of proposal values, totally ordered
CONSTANT Bottom       \* special value not in Values

\* ----------------------------------------------------------------------
\* Enumerations
\* ----------------------------------------------------------------------
Locs == {"Bcast1", "Wait1", "Bcast2", "Wait2", "Done", "Crashed", "Choosing"}

MsgType == {"Phase1", "Phase2"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    loc,            \* [proc -> location]
    prop,           \* [proc -> value]  (initial proposals)
    view,           \* [proc -> [proc -> value]]  (local views)
    est,            \* [proc -> value]  (estimated value after Phase1)
    decision,       \* [proc -> value]  (final decision, Bottom if none)
    crashedCount,   \* number of processes that have crashed
    sent,           \* set of all messages ever sent
    received        \* [proc -> SUBSET sent]  (messages each proc has received)

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N
Msg == [type : MsgType, sender : Proc, prop : Values, est : Values \cup {Bottom}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Message1(p) == [type |-> "Phase1", sender |-> p, prop |-> prop[p], est |-> Bottom]
Message2(p) == [type |-> "Phase2", sender |-> p, prop |-> prop[p], est |-> est[p]]

CountDistinctSenders(ms) ==
    Cardinality({ m["sender"] : m \in ms })

MaxInView(v) ==
    IF \E x \in Values : x # Bottom then
        CHOOSE x \in Values : \A y \in Values : y # Bottom => y <= x
    ELSE Bottom

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ loc = [p \in Proc |-> "Bcast1"]
    /\ prop \in [Proc -> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
    /\ loc[p] = "Bcast1"
    /\ sent' = sent \cup { Message1(p) }
    /\ loc' = [loc EXCEPT ![p] = "Wait1"]
    /\ UNCHANGED << prop, view, est, decision, crashedCount, received >>

ReceivePhase1(p, m) ==
    /\ loc[p] = "Wait1"
    /\ m \in sent
    /\ m.type = "Phase1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED << loc, prop, est, decision, crashedCount, sent >>

ComputeEst(p) ==
    /\ loc[p] = "Wait1"
    /\ CountDistinctSenders(received[p]) >= N - T
    /\ est' = [est EXCEPT ![p] = MaxInView(view[p])]
    /\ loc' = [loc EXCEPT ![p] = "Bcast2"]
    /\ UNCHANGED << prop, view, decision, crashedCount, sent, received >>

BroadcastPhase2(p) ==
    /\ loc[p] = "Bcast2"
    /\ sent' = sent \cup { Message2(p) }
    /\ loc' = [loc EXCEPT ![p] = "Wait2"]
    /\ UNCHANGED << prop, view, est, decision, crashedCount, received >>

ReceivePhase2(p, m) ==
    /\ loc[p] = "Wait2"
    /\ m \in sent
    /\ m.type = "Phase2"
    /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED << loc, prop, est, decision, crashedCount, sent >>

DecideOnCommonEst(p) ==
    /\ loc[p] = "Wait2"
    /\ \E v \in Values :
        CountDistinctSenders({ m \in received[p] : m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << prop, view, est, crashedCount, sent, received >>

MoveToChoosing(p) ==
    /\ loc[p] = "Wait2"
    /\ \A v \in Values :
        CountDistinctSenders({ m \in received[p] : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ CountDistinctSenders({ m \in received[p] : m.type = "Phase2" }) = N
    /\ loc' = [loc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED << prop, view, est, decision, crashedCount, sent, received >>

ChooseAndDecide(p) ==
    /\ loc[p] = "Choosing"
    /\ est' = [est EXCEPT ![p] = MaxInView(view[p])]
    /\ decision' = [decision EXCEPT ![p] = est[p]]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << prop, view, crashedCount, sent, received >>

Crash(p) ==
    /\ loc[p] # "Crashed"
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "Crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED << prop, view, est, decision, sent, received >>

Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in Proc : DecideOnCommonEst(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< loc, prop, view, est, decision,
                         crashedCount, sent, received >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashedCount \in Nat
    /\ crashedCount <= N
    /\ sent \subseteq Msg
    /\ received \in [Proc -> SUBSET sent]

Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* Theorem (optional, helps TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====