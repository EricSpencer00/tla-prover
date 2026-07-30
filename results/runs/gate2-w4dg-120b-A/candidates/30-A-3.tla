---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, dec, crashedCount, msgs, recv

vars == <<loc, view, prop, est, dec, crashedCount, msgs, recv>>

MsgTypes == {"phase1", "phase2"}

Phases == {"b1", "w1", "prep", "b2", "w2", "done", "crash", "choose"}

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ msgs \subseteq [type: MsgTypes, val: Values, from: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ dec = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ msgs = {}
  /\ recv = [i \in 1..N |-> {}]

BroadcastPhase1(i) ==
  /\ loc[i] = "b1"
  /\ msgs' = msgs \cup {[type |-> "phase1", val |-> prop[i], from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase1(i, m) ==
  /\ loc[i] = "w1"
  /\ m \in msgs
  /\ m.type = "phase1"
  /\ m.from \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.from}]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, msgs>>

ComputeEst(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality(recv[i]) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE x \in Values :
                            \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= x]
  /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, prop, dec, crashedCount, msgs, recv>>

BroadcastPhase2(i) ==
  /\ loc[i] = "b2"
  /\ msgs' = msgs \cup {[type |-> "phase2", val |-> prop[i], from |-> i, est |-> est[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, recv>>

ReceivePhase2(i, m) ==
  /\ loc[i] = "w2"
  /\ m \in msgs
  /\ m.type = "phase2"
  /\ m.from \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.from}]
  /\ UNCHANGED <<loc, prop, est, dec, crashedCount, msgs>>

DecideOnThreshold(i) ==
  /\ loc[i] = "w2"
  /\ \E v \in Values : Cardinality({j \in recv[i] : view[i][j] = v}) >= N - T
  /\ dec' = [dec EXCEPT ![i] = CHOOSE v \in Values :
                            Cardinality({j \in recv[i] : view[i][j] = v}) >= N - T]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, msgs, recv>>

ChooseState(i) ==
  /\ loc[i] = "w2"
  /\ recv[i] = 1..N
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, dec, crashedCount, msgs, recv>>

ChooseValue(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
        /\ \E j \in 1..N : view[i][j] = v
        /\ dec' = [dec EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, msgs, recv>>

Crash(i) ==
  /\ loc[i] \notin {"crash", "done"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![i] = "crash"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, dec, msgs, recv>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i) \/ ComputeEst(i) \/ BroadcastPhase2(i)
                        \/ DecideOnThreshold(i) \/ ChooseState(i) \/ ChooseValue(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in msgs : ReceivePhase1(i, m) \/ ReceivePhase2(i, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in msgs : ReceivePhase1(i, m))
  /\ WF_vars(\E i \in 1..N, m \in msgs : ReceivePhase2(i, m))
  /\ WF_vars(\E i \in 1..N : ComputeEst(i))
  /\ WF_vars(\E i \in 1..N : DecideOnThreshold(i))
  /\ WF_vars(\E i \in 1..N : ChooseState(i))
  /\ WF_vars(\E i \in 1..N : ChooseValue(i))

Validity == \A i \in 1..N : dec[i] # Bottom => \E j \in 1..N : dec[i] = prop[j]

Agreement == \A i, j \in 1..N : (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crash"})

ConditionC1 ==
  (Cardinality({i \in 1..N : \A j \in 1..N : prop[i] >= prop[j]}) >= F + 1) ~> Termination

====