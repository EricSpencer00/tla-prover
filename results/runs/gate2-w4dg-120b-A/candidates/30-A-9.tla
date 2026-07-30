---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ T >= F
       /\ 2 * T < N
       /\ Bottom \notin Values

MsgTypes == {"ph1", "ph2"}

VARIABLES loc, view, prop, est, decided, crashedCount, msgs, recvAll

vars == <<loc, view, prop, est, decided, crashedCount, msgs, recvAll>>

TypeOK ==
  /\ loc \in [1..N -> {"ph1", "ph1w", "prep", "ph2", "ph2w", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ msgs \subseteq [type : MsgTypes, val : Values, sender : 1..N, v2 : Values \cup {Bottom}]
  /\ recvAll \in [1..N -> SUBSET [type : MsgTypes, val : Values, sender : 1..N, v2 : Values \cup {Bottom}]]

Init ==
  /\ loc = [p \in 1..N |-> "ph1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ \E f \in [1..N -> Values] : prop = f
  /\ est = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ msgs = {}
  /\ recvAll = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "ph1"
  /\ msgs' = msgs \cup {[type |-> "ph1", val |-> prop[p], sender |-> p, v2 |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "ph1w"]
  /\ UNCHANGED <<view, prop, est, decided, crashedCount, recvAll>>

ReceivePhase1(p) ==
  /\ loc[p] = "ph1w"
  /\ \E m \in msgs :
       /\ m.type = "ph1"
       /\ view[p][m.sender] = Bottom
       /\ view' = [view EXCEPT ![p][m.sender] = m.val]
       /\ recvAll' = [recvAll EXCEPT ![p] = recvAll[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashedCount, msgs>>

ComputeEstimate(p) ==
  /\ loc[p] = "ph1w"
  /\ Cardinality({m \in recvAll[p] : m.type = "ph1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values : \A y \in Values : (y \in {view[p][q] : q \in 1..N} /\ y # Bottom) => y <= x]
  /\ loc' = [loc EXCEPT ![p] = "ph2"]
  /\ UNCHANGED <<view, prop, decided, crashedCount, msgs, recvAll>>

BroadcastPhase2(p) ==
  /\ loc[p] = "ph2"
  /\ msgs' = msgs \cup {[type |-> "ph2", val |-> prop[p], sender |-> p, v2 |-> est[p]}
  /\ loc' = [loc EXCEPT ![p] = "ph2w"]
  /\ UNCHANGED <<view, prop, est, decided, crashedCount, recvAll>>

ReceivePhase2(p) ==
  /\ loc[p] = "ph2w"
  /\ \E m \in msgs :
       /\ m.type = "ph2"
       /\ view[p][m.sender] = Bottom
       /\ view' = [view EXCEPT ![p][m.sender] = m.val]
       /\ recvAll' = [recvAll EXCEPT ![p] = recvAll[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashedCount, msgs>>

DecideByThreshold(p) ==
  /\ loc[p] = "ph2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in recvAll[p] : m.type = "ph2" /\ m.v2 = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, msgs, recvAll>>

ChooseValue(p) ==
  /\ loc[p] = "ph2w"
  /\ \A v \in Values : Cardinality({m \in recvAll[p] : m.type = "ph2" /\ m.v2 = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decided, crashedCount, msgs, recvAll>>

DecideChosen(p) ==
  /\ loc[p] = "choose"
  /\ \E v \in Values :
       /\ v IN {view[p][q] : q \in 1..N}
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, msgs, recvAll>>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {"done", "crashed"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, decided, msgs, recvAll>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E p \in 1..N : ReceivePhase1(p)
  \/ \E p \in 1..N : ComputeEstimate(p)
  \/ \E p \in 1..N : BroadcastPhase2(p)
  \/ \E p \in 1..N : ReceivePhase2(p)
  \/ \E p \in 1..N : DecideByThreshold(p)
  \/ \E p \in 1..N : ChooseValue(p)
  \/ \E p \in 1..N : DecideChosen(p)
  \/ \E p \in 1..N : Crash(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : ReceivePhase1(p))
  /\ WF_vars(\E p \in 1..N : ComputeEstimate(p))
  /\ WF_vars(\E p \in 1..N : ReceivePhase2(p))
  /\ WF_vars(\E p \in 1..N : DecideChosen(p))

Validity == \A p \in 1..N : decided[p] # Bottom => decided[p] \in Values

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

C1 == Cardinality({p \in 1..N : prop[p] = CHOOSE x \in Values : \A y \in Values : y <= x}) >= F + 1

ConditionalTermination == C1 ~> Termination

====