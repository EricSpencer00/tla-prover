---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ (2 * T) < N
       /\ N > 0
       /\ 0 <= F /\ F <= T
       /\ Bottom \notin Values

Phases == { "phase1", "phase1Wait", "prepare", "phase2",
            "phase2Wait", "done", "crashed", "choose" }
Types == { "phase1", "phase2" }
Msgs == [kind : Types, val : Values, snd : 0 .. (N - 1), ev : Values \cup {Bottom}]
Views == [0 .. (N - 1) -> Values \cup {Bottom}]

VARIABLES control, view, prop, estimate, decision, crashedCount, sentMsgs, recvMsgs

vars == <<control, view, prop, estimate, decision, crashedCount, sentMsgs, recvMsgs>>

TypeOK ==
  /\ control \in [0 .. (N - 1) -> Phases]
  /\ view \in [0 .. (N - 1) -> Views]
  /\ prop \in [0 .. (N - 1) -> Values]
  /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ decision \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ crashedCount \in 0 .. F
  /\ sentMsgs \subseteq Msgs
  /\ recvMsgs \in [0 .. (N - 1) -> SUBSET Msgs]

Init ==
  /\ control = [i \in 0 .. (N - 1) |-> "phase1"]
  /\ view = [i \in 0 .. (N - 1) |-> [j \in 0 .. (N - 1) |-> Bottom]]
  /\ prop \in [0 .. (N - 1) -> Values]
  /\ estimate = [i \in 0 .. (N - 1) |-> Bottom]
  /\ decision = [i \in 0 .. (N - 1) |-> Bottom]
  /\ crashedCount = 0
  /\ sentMsgs = {}
  /\ recvMsgs = [i \in 0 .. (N - 1) |-> {}]

MaxValue(r) == CHOOSE x \in Values : \A y \in Values : y <= x

\* Phase 1: broadcast each process's proposal.
BroadcastPhase1(i) ==
  /\ control[i] = "phase1"
  /\ sentMsgs' = sentMsgs \cup {[kind |-> "phase1", val |-> prop[i], snd |-> i, ev |-> Bottom]}
  /\ control' = [control EXCEPT ![i] = "phase1Wait"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recvMsgs>>

\* Receiving a phase-matched message updates the local view.
ReceivePhase1(i, m) ==
  /\ control[i] = "phase1Wait"
  /\ m.kind = "phase1"
  /\ m \notin recvMsgs[i]
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ UNCHANGED <<control, prop, estimate, decision, crashedCount, sentMsgs>>

\* After collecting enough phase-1 messages, compute the estimate.
Prepare(i) ==
  /\ control[i] = "phase1Wait"
  /\ Cardinality({m \in recvMsgs[i] : m.kind = "phase1"}) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![i] = MaxValue({view[i][j] : j \in 0 .. (N - 1)} \cup {prop[i]})]
  /\ control' = [control EXCEPT ![i] = "prepare"]
  /\ UNCHANGED <<view, prop, decision, crashedCount, sentMsgs, recvMsgs>>

BroadcastPhase2(i) ==
  /\ control[i] = "prepare"
  /\ sentMsgs' = sentMsgs \cup {[kind |-> "phase2", val |-> prop[i],
                     snd |-> i, ev |-> estimate[i]]}
  /\ control' = [control EXCEPT ![i] = "phase2Wait"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recvMsgs>>

ReceivePhase2(i, m) ==
  /\ control[i] = "phase2Wait"
  /\ m.kind = "phase2"
  /\ m \notin recvMsgs[i]
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.snd] = m.ev]
  /\ UNCHANGED <<control, prop, estimate, decision, crashedCount, sentMsgs>>

\* Decide once enough phase-2 messages agree on the same estimate.
Decide(i) ==
  /\ control[i] = "phase2Wait"
  /\ \E V \in Values :
       /\ Cardinality({m \in recvMsgs[i] : m.kind = "phase2" /\ m.ev = V}) >= (N - T)
       /\ decision' = [decision EXCEPT ![i] = V]
  /\ control' = [control EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashedCount, sentMsgs, recvMsgs>>

\* Deterministically pick from the local view when no estimate reached the threshold.
Choose(i) ==
  /\ control[i] = "phase2Wait"
  /\ \A V \in Values :
       Cardinality({m \in recvMsgs[i] : m.kind = "phase2" /\ m.ev = V}) < (N - T)
  /\ \E v \in Values :
       /\ v \in {view[i][j] : j \in 0 .. (N - 1)}
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ control' = [control EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, crashedCount, sentMsgs, recvMsgs>>

Crash(i) ==
  /\ control[i] \notin {"crashed", "done"}
  /\ crashedCount < F
  /\ control' = [control EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, estimate, decision, sentMsgs, recvMsgs>>

Next ==
  \/ \E i \in 0 .. (N - 1) : BroadcastPhase1(i) \/ Prepare(i) \/ BroadcastPhase2(i)
                             \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 0 .. (N - 1), m \in Msgs : ReceivePhase1(i, m) \/ ReceivePhase2(i, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 0 .. (N - 1), m \in Msgs : ReceivePhase1(i, m))
        /\ WF_vars(\E i \in 0 .. (N - 1), m \in Msgs : ReceivePhase2(i, m))
        /\ WF_vars(\E i \in 0 .. (N - 1) : Prepare(i))
        /\ WF_vars(\E i \in 0 .. (N - 1) : BroadcastPhase2(i))
        /\ WF_vars(\E i \in 0 .. (N - 1) : Decide(i))
        /\ WF_vars(\E i \in 0 .. (N - 1) : Choose(i))

Validity == \A i \in 0 .. (N - 1) : decision[i] # Bottom => decision[i] \in Values

Agreement == \A i, j \in 0 .. (N - 1) : (decision[i] # Bottom /\ decision[j] # Bottom)
                                      => decision[i] = decision[j]

Termination == <>(\A i \in 0 .. (N - 1) : control[i] \in {"done", "crashed"})

ConditionC1 ==
  /\ Cardinality({i \in 0 .. (N - 1) : prop[i] = MaxValue(Values)}) >= (F + 1)
  => Termination

Properties == Termination /\ ConditionC1

====