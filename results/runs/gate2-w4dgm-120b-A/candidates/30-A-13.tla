---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Processes == 0 .. (N - 1)

VARIABLES phase, view, proposed, estimate, decision, crashed, sent, received

vars == <<phase, view, proposed, estimate, decision, crashed, sent, received>>

TypeOK ==
    /\ phase \in [Processes -> {"phase1", "wait1", "prepare", "phase2", "wait2", "done", "crashed", "choose"}]
    /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
    /\ proposed \in [Processes -> Values]
    /\ estimate \in [Processes -> Values \cup {Bottom}]
    /\ decision \in [Processes -> Values \cup {Bottom}]
    /\ crashed \in 0 .. N
    /\ sent \subseteq [kind: {"phase1", "phase2"}, val: Values, from: Processes, est: Values \cup {Bottom}]
    /\ received \in [Processes -> SUBSET [kind: {"phase1", "phase2"}, val: Values, from: Processes, est: Values \cup {Bottom}]]

Init ==
    /\ phase = [p \in Processes |-> "phase1"]
    /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
    /\ proposed \in [Processes -> Values]
    /\ estimate = [p \in Processes |-> Bottom]
    /\ decision = [p \in Processes |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ received = [p \in Processes |-> {}]

\* Phase 1: each process broadcasts its own proposed value.
BroadcastPhase1(p) ==
    /\ phase[p] = "phase1"
    /\ sent' = sent \cup {[kind |-> "phase1", val |-> proposed[p], from |-> p, est |-> Bottom]}
    /\ phase' = [phase EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashed, received>>

\* A live process receives any message it has not yet processed.
Receive(p, m) ==
    /\ phase[p] \in {"wait1", "wait2"}
    /\ m \in sent
    /\ m.from \notin {r.from : r \in received[p]}
    /\ m.kind = phase[p]
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ received' = [received EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<phase, proposed, estimate, decision, crashed, sent>>

\* Once phase-1 messages from enough senders are in, compute the maximum estimate.
ReadyPhase1(p) ==
    /\ phase[p] = "wait1"
    /\ Cardinality({r.from : r \in received[p]}) >= N - T
    /\ estimate[p] = Bottom
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                        \A q \in Processes : view[p][q] # Bottom => view[p][q] <= v]
    /\ phase' = [phase EXCEPT ![p] = "prepare"]
    /\ UNCHANGED <<view, proposed, decision, crashed, sent, received>>

\* Phase 2: broadcast both the proposed value and the computed estimate.
BroadcastPhase2(p) ==
    /\ phase[p] = "prepare"
    /\ sent' = sent \cup {[kind |-> "phase2", val |-> proposed[p], from |-> p, est |-> estimate[p]]}
    /\ phase' = [phase EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashed, received>>

\* Decide on a value that at least N-T phase-2 messages agree on.
DecideAgree(p) ==
    /\ phase[p] = "wait2"
    /\ \E c \in Values :
        /\ Cardinality({r \in received[p] : r.kind = "phase2" /\ r.est = c}) >= N - T
        /\ decision' = [decision EXCEPT ![p] = c]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

\* Fallback: if all phase-2 messages have been received but no N-T agreement holds,
\* choose any locally-seen value and finish.
DecideChoose(p) ==
    /\ phase[p] = "wait2"
    /\ \A r \in received[p] : r.kind = "phase2"
    /\ \A c \in Values : Cardinality({r \in received[p] : r.kind = "phase2" /\ r.est = c}) < N - T
    /\ phase' = [phase EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

Chosen(p) ==
    /\ phase[p] = "choose"
    /\ \E c \in Values :
        /\ \E q \in Processes : view[p][q] = c
        /\ decision' = [decision EXCEPT ![p] = c]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

Crash(p) ==
    /\ phase[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, proposed, estimate, decision, sent, received>>

Next ==
    \/ \E p \in Processes : BroadcastPhase1(p) \/ ReadyPhase1(p) \/ BroadcastPhase2(p)
                          \/ DecideAgree(p) \/ DecideChoose(p) \/ Chosen(p) \/ Crash(p)
    \/ \E p \in Processes, m \in sent : Receive(p, m)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Processes, m \in sent : Receive(p, m))
    /\ WF_vars(\E p \in Processes : ReadyPhase1(p))
    /\ WF_vars(\E p \in Processes : BroadcastPhase2(p))
    /\ WF_vars(\E p \in Processes : DecideAgree(p))
    /\ WF_vars(\E p \in Processes : DecideChoose(p))
    /\ WF_vars(\E p \in Processes : Chosen(p))

\* Decision values come from the set of proposals, never invented.
Validity == \A p \in Processes : decision[p] # Bottom => \E q \in Processes : decision[p] = proposed[q]

\* The two actions that finish a process must agree on one value.
Agreement == \A p, q \in Processes : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Under the strong condition C1 (enough maximum proposals), every process finishes.
ConditionC1 == (\E q \in Processes : proposed[q] = CHOOSE v \in Values : \A q2 \in Processes : proposed[q2] <= v)
                => (\A p \in Processes : phase[p] \in {"done", "crashed"})

====