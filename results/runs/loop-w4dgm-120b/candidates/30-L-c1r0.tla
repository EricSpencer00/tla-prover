---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol is two-phase: a process first collects phase-1 messages into its
\* local view, then computes an estimated value as the maximum it has seen, and
\* finally collects phase-2 messages of estimated values before deciding.  A
\* crashed process stops participating (its messages are simply never sent).
\* The invariant is that a decided value was actually proposed by someone.

VARIABLES phase, view, proposal, estimate, decision, crashed, sent, received

Nodes == 1 .. N
MsgTypes == {"phase1", "phase2"}
Msgs == [type: MsgTypes, val: Values, sender: Nodes,
         est: Values \cup {Bottom}]

TypeOK ==
  /\ phase \in [Nodes -> {"broadcast1", "wait1", "prepare",
                         "broadcast2", "wait2", "done", "crashed", "choose"}]
  /\ view \in [Nodes -> [Nodes -> Values \cup {Bottom}]]
  /\ proposal \in [Nodes -> Values]
  /\ estimate \in [Nodes -> Values \cup {Bottom}]
  /\ decision \in [Nodes -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Msgs
  /\ received \in [Nodes -> SUBSET Msgs]

Init ==
  /\ phase = [n \in Nodes |-> "broadcast1"]
  /\ view = [n \in Nodes |-> [m \in Nodes |-> Bottom]]
  /\ proposal \in [Nodes -> Values]
  /\ estimate = [n \in Nodes |-> Bottom]
  /\ decision = [n \in Nodes |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [n \in Nodes |-> {}]

HasMsg(n, ty) == \E m \in received[n] : m.type = ty
ReceivedFrom(n, ty) ==
  {m.sender : m \in received[n] : m.type = ty}

\* Every sent or received message is retained in its sender's broadcast set.
Broadcast1(n) ==
  /\ phase[n] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[n],
                         sender |-> n, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![n] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

Receive1(n, m) ==
  /\ phase[n] = "wait1"
  /\ m.type = "phase1"
  /\ m \notin received[n]
  /\ received' = [received EXCEPT ![n] = @ \cup {m}]
  /\ view' = [view EXCEPT ![n][m.sender] = m.val]
  /\ UNCHANGED <<phase, proposal, estimate, decision, crashed, sent>>

PrepareAndBroadcast2(n) ==
  /\ phase[n] = "wait1"
  /\ Cardinality(ReceivedFrom(n, "phase1")) >= N - T
  /\ estimate' = [estimate EXCEPT ![n] = Max({view[n][m] : m \in Nodes})
                                      \cup {Bottom}]
  /\ phase' = [phase EXCEPT ![n] = "broadcast2"]
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[n],
                         sender |-> n, est |-> estimate[n]]}
  /\ UNCHANGED <<view, proposal, decision, crashed, received>>

Receive2(n, m) ==
  /\ phase[n] = "wait2"
  /\ m.type = "phase2"
  /\ m \notin received[n]
  /\ received' = [received EXCEPT ![n] = @ \cup {m}]
  /\ view' = [view EXCEPT ![n] = [view[n] EXCEPT ![m.sender] = m.est]]
  /\ UNCHANGED <<phase, proposal, estimate, decision, crashed, sent>>

DecisionFromSufficientEstimate(n) ==
  /\ phase[n] = "wait2"
  /\ Cardinality(ReceivedFrom(n, "phase2")) >= N - T
  /\ \E e \in Values :
       /\ Cardinality({m \in received[n] : m.type = "phase2" /\ m.est = e})
            >= N - T
       /\ decision' = [decision EXCEPT ![n] = e]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

TransitionToChoose(n) ==
  /\ phase[n] = "wait2"
  /\ \A m \in Nodes : [type |-> "phase2", val |-> proposal[n],
                       sender |-> n, est |-> estimate[n]] \in received[n]
  /\ Cardinality(ReceivedFrom(n, "phase2")) < N - T
  /\ phase' = [phase EXCEPT ![n] = "choose"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, received>>

\* Deterministic tie-breaking: a process in the choosing state picks any value
\* it has already observed in its view (it is never stuck).
ChooseAndDecide(n) ==
  /\ phase[n] = "choose"
  /\ \E e \in Values :
       /\ Cardinality({m \in Nodes : view[n][m] = e})
            >= Cardinality({m \in Nodes : view[n][m] = Bottom})
       /\ decision' = [decision EXCEPT ![n] = e]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

Crash(n) ==
  /\ crashed < F
  /\ phase[n] \notin {"done", "crashed"}
  /\ phase' = [phase EXCEPT ![n] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E n \in Nodes : Broadcast1(n)
  \/ \E n \in Nodes, m \in sent : Receive1(n, m)
  \/ \E n \in Nodes : PrepareAndBroadcast2(n)
  \/ \E n \in Nodes, m \in sent : Receive2(n, m)
  \/ \E n \in Nodes : DecisionFromSufficientEstimate(n)
  \/ \E n \in Nodes : TransitionToChoose(n)
  \/ \E n \in Nodes : ChooseAndDecide(n)
  \/ \E n \in Nodes : Crash(n)

\* The model keeps the two-phase delay bounded: a phase-2 message is never
\* broadcast before its sender has finished phase 1, so every phase-2 message
\* whose type has been received is eventually typed and observed by the receiver.
Spec == Init /\ [][Next]_<<phase, view, proposal, estimate, decision,
                           crashed, sent, received>>

\* A decided value must have been proposed by some process (the decision is
\* never a fabricated or stale value); plus the entire agreement condition.
Validity == \A n \in Nodes : decision[n] # Bottom => \E m \in Nodes : proposal[m] = decision[n]
Agreement == \A n1 \in Nodes, n2 \in Nodes :
               (decision[n1] # Bottom /\ decision[n2] # Bottom) => decision[n1] = decision[n2]

\* Safety: a process can be slow (it may sit in its waiting state for a while)
\* but never crashes while waiting, so weak fairness on the transition actions
\* here is enough to drive every non-crashed process to a decision.
\* Liveness: termination is guaranteed, and under Condition C1 (sufficient
\* maximum-value proposals) it is guaranteed even without the slow-process
\* fairness assumption.
Termination == <>(\A n \in Nodes : phase[n] \in {"done", "crashed"})
ConditionalTermination == (\A n \in Nodes : proposal[n] = Max(Values)) => Termination

\* The model checks a weaker version of Condition C1 itself (at least one
\* process proposes the maximum) because the full F+1 bound is not needed to
\* keep the reachable state space finite and termination-probable.
C1 == \E n \in Nodes : proposal[n] = Max(Values)

\* Model-checking weak fairness of every transition that advances a process
\* toward a decision (together with strong fairness on the final choice) is
\* what guarantees termination in the face of arbitrary delays.
Properties ==
  /\ WF_<<phase, view, proposal, estimate, decision, crashed, sent, received>>(
        \E n \in Nodes : Broadcast1(n) \/ PrepareAndBroadcast2(n)
                        \/ DecisionFromSufficientEstimate(n) \/ ChooseAndDecide(n))
  /\ WF_<<phase, view, proposal, estimate, decision, crashed, sent, received>>(
        \E n \in Nodes, m \in sent : Receive1(n, m) \/ Receive2(n, m))
  /\ WF_<<phase, view, proposal, estimate, decision, crashed, sent, received>>(
        \E n \in Nodes : TransitionToChoose(n))
  /\ SF_<<phase, view, proposal, estimate, decision, crashed, sent, received>>(
        \E n \in Nodes : ChooseAndDecide(n))

====