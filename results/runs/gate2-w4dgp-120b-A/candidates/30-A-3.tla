---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME T \in Nat /\ F \in Nat /\ N \in Nat /\ T > 0 /\ F >= 0 /\ 2 * T < N /\ Bottom \notin Values

MessageTypes == {"phase1", "phase2"}
Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choose"}
Msgs == [type : MessageTypes, val : Values, snd : 1 .. N, est : Values \cup {Bottom}]

VARIABLES pc, view, prop, est, decision, crashedCount, sent, recv

vars == <<pc, view, prop, est, decision, crashedCount, sent, recv>>

InitView == [i \in 1 .. N |-> Bottom]

TypeOK ==
    /\ pc \in [1 .. N -> Phases]
    /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
    /\ prop \in [1 .. N -> Values]
    /\ est \in [1 .. N -> Values \cup {Bottom}]
    /\ decision \in [1 .. N -> Values \cup {Bottom}]
    /\ crashedCount \in 0 .. F
    /\ sent \subseteq Msgs
    /\ recv \in [1 .. N -> SUBSET Msgs]

Init ==
    /\ pc = [n \in 1 .. N |-> "broadcast1"]
    /\ view = [n \in 1 .. N |-> InitView]
    /\ prop \in [1 .. N -> Values]
    /\ est = [n \in 1 .. N |-> Bottom]
    /\ decision = [n \in 1 .. N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [n \in 1 .. N |-> {}]

MaxVal(n) == CHOOSE m \in Values : \A x \in Values : x <= m /\ x \in {view[n][j] : j \in 1 .. N /\ view[n][j] # Bottom}

Count(m) == Cardinality({n \in 1 .. N : prop[n] = m})

BroadcastPhase1(n) ==
    /\ pc[n] = "broadcast1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[n], snd |-> n, est |-> Bottom]}
    /\ pc' = [pc EXCEPT ![n] = "wait1"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

ReceivePhase1(n, m) ==
    /\ pc[n] \in {"wait1", "prepare"}
    /\ m \in sent
    /\ m.type = "phase1"
    /\ view[n][m.snd] = Bottom
    /\ view' = [view EXCEPT ![n][m.snd] = m.val]
    /\ recv' = [recv EXCEPT ![n] = @ \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashedCount, sent>>

ComputeEstimate(n) ==
    /\ pc[n] = "wait1"
    /\ Cardinality({m \in recv[n] : m.type = "phase1"}) >= N - T
    /\ est' = [est EXCEPT ![n] = MaxVal(n)]
    /\ pc' = [pc EXCEPT ![n] = "broadcast2"]
    /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recv>>

BroadcastPhase2(n) ==
    /\ pc[n] = "broadcast2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[n], snd |-> n, est |-> est[n]]}
    /\ pc' = [pc EXCEPT ![n] = "wait2"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

ReceivePhase2(n, m) ==
    /\ pc[n] = "wait2"
    /\ m \in sent
    /\ m.type = "phase2"
    /\ view[n][m.snd] = Bottom
    /\ view' = [view EXCEPT ![n][m.snd] = m.val]
    /\ recv' = [recv EXCEPT ![n] = @ \cup {m}]
    /\ UNCHANGED <<pc, prop, est, decision, crashedCount, sent>>

Decide(n) ==
    /\ pc[n] = "wait2"
    /\ \E v \in Values :
        /\ Cardinality({m \in recv[n] : m.type = "phase2" /\ m.est = v}) >= N - T
        /\ decision' = [decision EXCEPT ![n] = v]
    /\ pc' = [pc EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Choose(n) ==
    /\ pc[n] = "wait2"
    /\ \A m \in recv[n] : m.type = "phase2"
    /\ pc' = [pc EXCEPT ![n] = "choose"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, sent, recv>>

DeterministicChoose(n) ==
    /\ pc[n] = "choose"
    /\ \E v \in Values :
        /\ \E j \in 1 .. N :
            view[n][j] = v /\ decision' = [decision EXCEPT ![n] = v]
    /\ pc' = [pc EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Crash(n) ==
    /\ pc[n] \notin {"done", "crashed"}
    /\ crashedCount < F
    /\ pc' = [pc EXCEPT ![n] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
    \/ \E n \in 1 .. N :
         BroadcastPhase1(n) \/ ComputeEstimate(n) \/ BroadcastPhase2(n) \/ Decide(n)
         \/ Choose(n) \/ DeterministicChoose(n) \/ Crash(n)
    \/ \E n \in 1 .. N, m \in Msgs :
         ReceivePhase1(n, m) \/ ReceivePhase2(n, m)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E n \in 1 .. N, m \in Msgs : ReceivePhase1(n, m))
    /\ WF_vars(\E n \in 1 .. N, m \in Msgs : ReceivePhase2(n, m))
    /\ WF_vars(\E n \in 1 .. N : ComputeEstimate(n))
    /\ WF_vars(\E n \in 1 .. N : Decide(n))
    /\ WF_vars(\E n \in 1 .. N : Choose(n))
    /\ WF_vars(\E n \in 1 .. N : DeterministicChoose(n))

Validity == \A n \in 1 .. N : decision[n] # Bottom => (\E m \in 1 .. N : prop[m] = decision[n])

Agreement == \A n, m \in 1 .. N : (decision[n] # Bottom /\ decision[m] # Bottom) => decision[n] = decision[m]

Terminate == \A n \in 1 .. N : (pc[n] \in {"done", "crashed"}) \U (pc[n] # "choose")

TerminateC1 == (Cardinality({n \in 1 .. N : prop[n] = MaxVal(1)}) > F) ~> (\A n \in 1 .. N : pc[n] \in {"done", "crashed"})

====