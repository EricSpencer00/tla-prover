---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, decision, crashedCount, sent, recvd

MsgPhases == {"ph1", "ph2"}
AllVals == Values \cup {Bottom}
Phases == {"ph1bro", "ph1wait", "preph2", "ph2bro", "ph2wait", "done", "crashed", "choosing"}

TypeOK ==
    /\ loc \in [1..N -> Phases]
    /\ view \in [1..N -> [1..N -> AllVals]]
    /\ prop \in [1..N -> AllVals]
    /\ est \in [1..N -> AllVals]
    /\ decision \in [1..N -> AllVals]
    /\ crashedCount \in 0..N
    /\ sent \subseteq [type: MsgPhases, val: AllVals, sender: 1..N, e: AllVals]
    /\ recvd \in [1..N -> SUBSET [type: MsgPhases, val: AllVals, sender: 1..N, e: AllVals]]

Init ==
    /\ loc = [p \in 1..N |-> "ph1bro"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recvd = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
    /\ loc[p] = "ph1bro"
    /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], sender |-> p, e |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "ph1wait"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recvd>>

ReceivePhase1(p, m) ==
    /\ loc[p] = "ph1wait"
    /\ m \in sent
    /\ m.type = "ph1"
    /\ view[p][m.sender] = Bottom
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED <<loc, prop, est, decision, crashedCount, sent, recvd>>

Estimate(p) ==
    /\ loc[p] = "ph1wait"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values :
                    \A y \in Values : (y \in {view[p][q] : q \in 1..N} => y <= x)]
    /\ loc' = [loc EXCEPT ![p] = "ph2bro"]
    /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recvd>>

BroadcastPhase2(p) ==
    /\ loc[p] = "ph2bro"
    /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], sender |-> p, e |-> est[p]}
                          \cup {m \in recvd[p] : m.type = "ph1"}
                          \cup {m \in recvd[p] : m.type = "ph2"}}
    /\ loc' = [loc EXCEPT ![p] = "ph2wait"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, recvd>>

ReceivePhase2(p, m) ==
    /\ loc[p] = "ph2wait"
    /\ m \in sent
    /\ m.type = "ph2"
    /\ loc' = loc
    /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup {m}]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, sent>>

DecideViaC2(p) ==
    /\ loc[p] = "ph2wait"
    /\ Cardinality({m \in recvd[p] : m.type = "ph2" /\ m.e = est[p]}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = est[p]]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recvd>>

MoveToChoosing(p) ==
    /\ loc[p] = "ph2wait"
    /\ {m.type : m \in recvd[p]} \subseteq {"ph1", "ph2"}
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) = N
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decision, crashedCount, sent, recvd>>

ChooseDeterministic(p) ==
    /\ loc[p] = "choosing"
    /\ \E x \in Values :
        /\ decision' = [decision EXCEPT ![p] = x]
        /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashedCount, sent, recvd>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashedCount < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<view, prop, est, decision, sent, recvd>>

Next ==
    \/ \E p \in 1..N : BroadcastPhase1(p)
    \/ \E p \in 1..N, m \in sent : ReceivePhase1(p, m)
    \/ \E p \in 1..N : Estimate(p)
    \/ \E p \in 1..N : BroadcastPhase2(p)
    \/ \E p \in 1..N, m \in sent : ReceivePhase2(p, m)
    \/ \E p \in 1..N : DecideViaC2(p)
    \/ \E p \in 1..N : MoveToChoosing(p)
    \/ \E p \in 1..N : ChooseDeterministic(p)
    \/ \E p \in 1..N : Crash(p)

Spec ==
    /\ Init
    /\ [][Next]_<<loc, view, prop, est, decision, crashedCount, sent, recvd>>
    /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
    /\ WF_vars(\E p \in 1..N : \E m \in sent : ReceivePhase1(p, m))
    /\ WF_vars(\E p \in 1..N : Estimate(p))
    /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
    /\ WF_vars(\E p \in 1..N : \E m \in sent : ReceivePhase2(p, m))
    /\ WF_vars(\E p \in 1..N : DecideViaC2(p))
    /\ WF_vars(\E p \in 1..N : MoveToChoosing(p))
    /\ WF_vars(\E p \in 1..N : ChooseDeterministic(p))
    /\ WF_vars(\E p \in 1..N : Crash(p))

Validity ==
    \A p \in 1..N :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in 1..N :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
    \A p \in 1..N : (loc[p] = "crashed" \/ loc[p] = "done")

ConditionC1 ==
    Cardinality({p \in 1..N : prop[p] = CHOOSE x \in Values :
                    \A y \in Values : y \in {prop[q] : q \in 1..N} => y <= x}})
        >= F + 1

====