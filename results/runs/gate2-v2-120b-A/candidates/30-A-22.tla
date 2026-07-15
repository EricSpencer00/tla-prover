---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

\*--------------------------------------------------------------------
\* Derived constants
\*--------------------------------------------------------------------
Proc == 1..N
VMAX  == Max(Values) \* the globally maximum proposal value

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
MsgType == {"phase1", "phase2"}

Message == [type : MsgType,
            value : Values \cup {Bottom},
            sender : Proc,
            est   : Values \cup {Bottom}]

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES
    pc,          \* program counter (state) of each process
    prop,        \* proposed value of each process
    view,        \* local view matrix: view[p][q] is value of q known to p
    est,         \* estimated value of each process (max of its view)
    decision,    \* decision value of each process
    msgs_sent,   \* set of all messages that have been broadcast
    msgs_recv,   \* msgs_recv[p] is the set of messages received by p
    crashCount   \* number of crashed processes

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
StateSet == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

\* Initial state
Init ==
    /\ pc = [p \in Proc |-> "bcast1"]
    /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]  \* any value from Values
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ msgs_sent = {}
    /\ msgs_recv = [p \in Proc |-> {}]
    /\ crashCount = 0

\* Action: broadcast phase-1 message
Bcast1(p) ==
    /\ pc[p] = "bcast1"
    /\ let m == [type |-> "phase1",
                value |-> prop[p],
                sender |-> p,
                est |-> Bottom] in
       /\ msgs_sent' = msgs_sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<prop, view, est, decision, msgs_recv, crashCount>>

\* Action: receive a phase-1 message
Recv1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in msgs_sent :
          /\ m.type = "phase1"
          /\ m.sender # p
          /\ view[p][m.sender] = Bottom   \* not yet recorded
          /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ UNCHANGED <<pc, prop, est, decision, msgs_sent, msgs_recv, crashCount>>

\* Action: after collecting enough phase-1 messages, compute est and go to phase2 broadcast
ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "bcast2"]
    /\ UNCHANGED <<prop, view, decision, msgs_sent, msgs_recv, crashCount>>

\* Action: broadcast phase-2 message
Bcast2(p) ==
    /\ pc[p] = "bcast2"
    /\ let m == [type |-> "phase2",
                value |-> prop[p],
                sender |-> p,
                est |-> est[p]] in
       /\ msgs_sent' = msgs_sent \cup {m}
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<prop, view, est, decision, msgs_recv, crashCount>>

\* Action: receive a phase-2 message
Recv2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in msgs_sent :
          /\ m.type = "phase2"
          /\ m.sender # p
          /\ msgs_recv' = [msgs_recv EXCEPT ![p] = msgs_recv[p] \cup {m}]
    /\ UNCHANGED <<pc, prop, view, est, decision, msgs_sent, crashCount>>

\* Action: decide when enough equal estimated values are seen
Decide(p) ==
    /\ pc[p] = "wait2"
    /\ \E v \in Values :
          /\ Cardinality({ m \in msgs_recv[p] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, msgs_sent, msgs_recv, crashCount>>

\* Action: move to choosing when all phase-2 messages received without a decision
MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ Cardinality({ m \in msgs_recv[p] : m.type = "phase2" }) = N
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<prop, view, est, decision, msgs_sent, msgs_recv, crashCount>>

\* Action: deterministic choosing from local view
Choose(p) ==
    /\ pc[p] = "choosing"
    /\ \E v \in Values :
          /\ v \in { view[p][q] : q \in Proc }
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in Values :
                                   v \in { view[p][q] : q \in Proc }]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<prop, view, est, msgs_sent, msgs_recv, crashCount>>

\* Action: crash a process
Crash(p) ==
    /\ pc[p] # "crashed"
    /\ crashCount < F
    /\ pc' = [pc EXCEPT ![p] = "crashed"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<prop, view, est, decision, msgs_sent, msgs_recv>>

\* Stuttering step for terminated or crashed processes
Idle ==
    /\ \E p \in Proc :
          /\ pc[p] \in {"done", "crashed"}
    /\ UNCHANGED <<pc, prop, view, est, decision, msgs_sent, msgs_recv, crashCount>>

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Bcast1(p)
    \/ \E p \in Proc : Recv1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Bcast2(p)
    \/ \E p \in Proc : Recv2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choose(p)
    \/ \E p \in Proc : Crash(p)
    \/ Idle

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, prop, view, est, decision, msgs_sent, msgs_recv, crashCount>>

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> StateSet]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ msgs_sent \subseteq Message
    /\ msgs_recv \in [Proc -> SUBSET Message]
    /\ crashCount \in Nat
    /\ crashCount <= F

\*--------------------------------------------------------------------
\* Safety properties
\*--------------------------------------------------------------------
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

\*--------------------------------------------------------------------
\* Theorems (optional, for readability)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Validity
THEOREM Spec => []Agreement

====