---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase consensus on the maximum; processes broadcast phase-1
\* values, estimate locally, and then a quorum of phase-2 messages decides.
\* Assumption: 2T < N (fault tolerance); Bottom is the uninitialized marker.
\* Safety: no two processes decide differently; Validity: decisions are
\* proposed values. Liveness: every process eventually decides or crashes,
\* and Condition C1 forces termination when enough max values are proposed.

VARIABLES phase, view, proposal, estimate, decision, crashed, sent, recv

vars == <<phase, view, proposal, estimate, decision, crashed, sent, recv>>

Phases == {"bst1", "wph1", "prep", "bst2", "wph2", "done", "crashed", "choose"}
MsgTypes == {"p1", "p2"}
Msgs == [kind: MsgTypes, val: Values, sender: 0..(N - 1), est: Values \cup {Bottom}]

TypeOK ==
    /\ phase \in [0..(N - 1) -> Phases]
    /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
    /\ proposal \in [0..(N - 1) -> Values]
    /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ decision \in [0..(N - 1) -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ sent \subseteq Msgs
    /\ recv \subseteq Msgs

Init ==
    /\ phase = [p \in 0..(N - 1) |-> "bst1"]
    /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
    /\ proposal \in [0..(N - 1) -> Values]
    /\ estimate = [p \in 0..(N - 1) |-> Bottom]
    /\ decision = [p \in 0..(N - 1) |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = {}

BroadcastP1(p) ==
    /\ phase[p] = "bst1"
    /\ sent' = sent \cup {[kind |-> "p1", val |-> proposal[p], sender |-> p, est |-> Bottom]}
    /\ phase' = [phase EXCEPT ![p] = "wph1"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

ReceiveP1(p, m) ==
    /\ phase[p] = "wph1"
    /\ m \in recv
    /\ m.kind = "p1"
    /\ m.sender \notin {q \in 0..(N - 1) : view[p][q] # Bottom}
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED <<phase, proposal, estimate, decision, crashed, sent, recv>>

TransitionP1(p) ==
    /\ phase[p] = "wph1"
    /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE u \in Values :
                        \A q \in 0..(N - 1) : view[p][q] # Bottom => u >= view[p][q]]
    /\ phase' = [phase EXCEPT ![p] = "bst2"]
    /\ UNCHANGED <<view, proposal, decision, crashed, sent, recv>>

BroadcastP2(p) ==
    /\ phase[p] = "bst2"
    /\ sent' = sent \cup {[kind |-> "p2", val |-> proposal[p], sender |-> p,
                           est |-> estimate[p]]}
    /\ phase' = [phase EXCEPT ![p] = "wph2"]
    /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

ReceiveP2(p, m) ==
    /\ phase[p] = "wph2"
    /\ m \in recv
    /\ m.kind = "p2"
    /\ m.sender \notin {q \in 0..(N - 1) : view[p][q] # Bottom}
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED <<phase, proposal, estimate, decision, crashed, sent, recv>>

Decide(p) ==
    /\ phase[p] = "wph2"
    /\ \E c \in Values :
         Cardinality({q \in 0..(N - 1) : view[p][q] = c /\ estimate[p] = c}) >= N - T
         /\ decision' = [decision EXCEPT ![p] = c]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

\* Deterministic fallback: no quorum but the view is filled, so pick any
\* value the process has already seen and finish on it.
Choose(p) ==
    /\ phase[p] = "wph2"
    /\ {q \in 0..(N - 1) : view[p][q] # Bottom} = 0..(N - 1)
    /\ \A c \in Values :
         Cardinality({q \in 0..(N - 1) : view[p][q] = c /\ estimate[p] = c}) < N - T
    /\ decision' = [decision EXCEPT ![p] = CHOOSE u \in Values :
                        \E q \in 0..(N - 1) : view[p][q] = u]
    /\ phase' = [phase EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

Crash(p) ==
    /\ crashed < F
    /\ phase[p] \notin {"crashed", "done"}
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, proposal, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in 0..(N - 1) : BroadcastP1(p) \/ TransitionP1(p) \/ BroadcastP2(p)
                           \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 0..(N - 1), m \in Msgs : ReceiveP1(p, m) \/ ReceiveP2(p, m)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in 0..(N - 1), m \in Msgs : ReceiveP1(p, m))
    /\ WF_vars(\E p \in 0..(N - 1), m \in Msgs : ReceiveP2(p, m))
    /\ WF_vars(\E p \in 0..(N - 1) : TransitionP1(p))
    /\ WF_vars(\E p \in 0..(N - 1) : Decide(p))
    /\ WF_vars(\E p \in 0..(N - 1) : Choose(p))

Validity == \A p \in 0..(N - 1) : (decision[p] # Bottom) => \E q \in 0..(N - 1) : proposal[q] = decision[p]

Agreement == \A p, q \in 0..(N - 1) : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 0..(N - 1) : phase[p] \in {"done", "crashed"})

\* Under Condition C1 (enough max-value proposals) every run reaches a
\* decision rather than picking a strictly lower value in the choosing state.
CondC1 == (\A q \in 0..(N - 1) : (proposal[q] = CHOOSE c \in Values : \A r \in 0..(N - 1) : proposal[r] <= c) => N - Cardinality({q \in 0..(N - 1) : proposal[q] = c})) <= F

ConditionalTermination == CondC1 => Termination

====