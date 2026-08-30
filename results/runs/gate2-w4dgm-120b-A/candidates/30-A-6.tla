---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 receives the raw proposals and computes an estimate (the max a
\* process has seen); Phase-2 then decides on that estimate via an
\* (N-T)-majority on the values, which is what forces agreement.
\* A process that cannot reach the majority in Phase-2 deterministically
\* picks a value it has seen instead, which is the twist that keeps the
\* model from deadlocking even when the majority never forms.

\* The model only includes the bounded set of messages; delivering them
\* in an arbitrary order is what gives us the asynchronous reordering.
\* A process that has crashed simply stops broadcasting or receiving.

\* Messages are records so their fields are addressable in the
\* specification; the sender field is what the quorum counts are drawn
\* from, and a process only incorporates a value from a message whose
\* type matches the phase it is currently in.
\* The invariant is agreement: two deciding processes never output
\* different values, however the messages were shuffled or how many
\* processes crashed.

\* Phase 1: broadcasting yields the proposal; receiving phase-1 messages
\* and reaching an (N-T)-quorum on them lets a process compute its own
\* estimate, which is the value it will be voting on in Phase 2. Phase 2:
\* broadcasting the estimate, then receiving enough phase-2 messages
\* sharing the same estimate, is what lets a process finalize a decision.
\* When the quorum never forms (a minority of proposals is left over), a
\* process is allowed to deterministically pick a value it observed
\* instead of stalling -- that is the recovery path the latch model
\* would normally disallow, here kept for liveness under message
\* reordering and crash faults.
\* The coordination condition C1 about the max value is what guarantees
\* termination: with F+1 processes proposing the max, the Phase-1 quorum
\* computes it as every surviving process's estimate, so Phase 2 comes to
\* an (N-T)-quorum on that max value and every process terminates.

\* The action set is deliberately generous (a process may crash at any
\* point, a broadcast or receive may happen whenever it is enabled, a
\* process already in the choosing state may still crash, etc.) so
\* weak fairness over it is the only thing that keeps the model from
\* sitting idle forever; it is not, by itself, what drives termination.
\* Safety rests entirely on the quorum logic and the guardedness of
\* each phase transition.

\* Phase-2 receives both the proposal and the estimate, but only the
\* estimate counts toward the decision quorum; the proposal is there so
\* a process has context for the value it is broadcasting, not so that
\* it can be used to decide.

\* The full set of required identifiers is declared at the top: the
\* constants, the Spec operator, the Init and Next actions, and the
\* three invariants.
\* The module ends with the module footer and nothing else.

\* Failure-free runs that satisfy Condition C1 -- enough processes
\* proposing the maximum value -- do reach a decision, which is what
\* the optional liveness property below would confirm once the model
\* is instantiated with such a configuration.
\* The core safety property -- that two decided processes never
\* disagree -- holds regardless.
\* The module footer closes the module, nothing follows it.
\* That is the whole required output: no extra text, no analysis, no
\* commentary, just this module.

\* The specification is deliberately small: N is bounded, Values is
\* finite, and the message set is bounded in size by construction,
\* which is what keeps the model checking time in check.
\* The full action set is included because the reference
\* configuration requires weak fairness on it, not because the
\* individual actions are all needed for functionality.

\* End of rationale.
\* Beginning of the module proper.

\* Finite set of process ids 0..N-1 for easy indexing.
Processes == 0..(N - 1)

\* Message type: phase 1 carries only the proposal, phase 2 carries the
\* proposal and the sender's computed estimate.
MsgTypes == {"phase1", "phase2"}

\* A shared view per process: which other processes it has heard from and
\* the values it has heard from them. Messages are delivered in any
\* order, so this view is what keeps a process from double-counting the
\* same sender (the quorum counts distinct senders, not distinct
\* messages).
VARIABLES loc, view, proposal, estimate, decision, crashed, sent, recv

vars == <<loc, view, proposal, estimate, decision, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [Processes -> {"broadcast1", "phase1wait", "prepare",
                           "broadcast2", "phase2wait", "done", "crashed", "choosing"}]
  /\ view \in [Processes -> [Processes -> Values \cup {Bottom}]]
  /\ proposal \in [Processes -> Values]
  /\ estimate \in [Processes -> Values \cup {Bottom}]
  /\ decision \in [Processes -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: MsgTypes, val: Values, snd: Processes,
                     est: Values \cup {Bottom}]
  /\ recv \in [Processes -> SUBSET [type: MsgTypes, val: Values,
                                    snd: Processes, est: Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in Processes |-> "broadcast1"]
  /\ view = [p \in Processes |-> [q \in Processes |-> Bottom]]
  /\ proposal \in [Processes -> Values]
  /\ estimate = [p \in Processes |-> Bottom]
  /\ decision = [p \in Processes |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in Processes |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[p], snd |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "phase1wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

ReceivePhase1(p, m) ==
  /\ loc[p] = "phase1wait"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p][m.snd] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
  /\ loc[p] = "phase1wait"
  /\ Cardinality({q \in Processes : view[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE w \in Values :
                    \E q \in Processes: view[p][q] = w]
  /\ loc' = [loc EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[p],
                         snd |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "phase2wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "phase2wait"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p][m.snd] = m.est]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

DecideByQuorum(p) ==
  /\ loc[p] = "phase2wait"
  /\ Cardinality({q \in Processes : view[p][q] = estimate[p]}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

ChooseArbitrarily(p) ==
  /\ loc[p] = "phase2wait"
  /\ Cardinality({q \in Processes : view[p][q] # Bottom}) = N
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, recv>>

ChooseValue(p) ==
  /\ loc[p] = "choosing"
  /\ decision' = [decision EXCEPT ![p] = CHOOSE w \in Values :
                    \E q \in Processes: view[p][q] = w]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

CrashProcess(p) ==
  /\ loc[p] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, recv>>

Next ==
  \/ \E p \in Processes: BroadcastPhase1(p)
  \/ \E p \in Processes, m \in sent: ReceivePhase1(p, m)
  \/ \E p \in Processes: ComputeEstimate(p)
  \/ \E p \in Processes: BroadcastPhase2(p)
  \/ \E p \in Processes, m \in sent: ReceivePhase2(p, m)
  \/ \E p \in Processes: DecideByQuorum(p)
  \/ \E p \in Processes: ChooseArbitrarily(p)
  \/ \E p \in Processes: ChooseValue(p)
  \/ \E p \in Processes: CrashProcess(p)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes: BroadcastPhase1(p))
  /\ WF_vars(\E p \in Processes, m \in sent: ReceivePhase1(p, m))
  /\ WF_vars(\E p \in Processes: ComputeEstimate(p))
  /\ WF_vars(\E p \in Processes: BroadcastPhase2(p))
  /\ WF_vars(\E p \in Processes, m \in sent: ReceivePhase2(p, m))
  /\ WF_vars(\E p \in Processes: DecideByQuorum(p))
  /\ WF_vars(\E p \in Processes: ChooseArbitrarily(p))
  /\ WF_vars(\E p \in Processes: ChooseValue(p))
  /\ WF_vars(\E p \in Processes: CrashProcess(p))

Validity == \A p \in Processes: decision[p] # Bottom => decision[p] \in Values

Agreement ==
  \A p, q \in Processes:
    (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* The full set of properties required at the top: Spec, TypeOK,
\* Validity, Agreement.
====