---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N > 0 /\ 2 * T < N /\ F >= 0 /\ F <= T /\ Bottom \notin Values

Types ==
    /\ N \in Nat
    /\ T \in Nat
    /\ F \in Nat
    /\ Values \subseteq Nat
    /\ Bottom \in Nat

MsgTypes == {"p1", "p2"}
Phases == {"ph1b", "ph1w", "ph2b", "ph2w", "done", "crashed", "choosing"}

VARIABLES phase, view, prop, estimate, decision, crashedCount, sent, recv

Dirty(p) ==
    /\ \E q \in 1..N : view[p][q] = Bottom
    /\ \E q \in 1..N : view[p][q] # Bottom

Init ==
    /\ phase = [p \in 1..N |-> "ph1b"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [p \in 1..N |-> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashedCount = 0
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

BroadcastPH1(p) ==
    /\ phase[p] = "ph1b"
    /\ sent' = sent \cup {[type |-> "p1", val |-> prop[p], sender |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "ph1w"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recv>>

BroadcastPH2(p) ==
    /\ phase[p] = "ph2b"
    /\ sent' = sent \cup {[type |-> "p2", val |-> prop[p], ev |-> estimate[p], sender |-> p]}
    /\ phase' = [phase EXCEPT ![p] = "ph2w"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, recv>>

ReceiveMsg(p, m) ==
    /\ phase[p] \in {"ph1w", "ph2w"}
    /\ m \in sent
    /\ m \notin recv[p]
    /\ m.sender # p
    /\ m.type = phase[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<phase, prop, estimate, decision, crashedCount, sent>>

ComputeEstimate(p) ==
    /\ phase[p] = "ph1w"
    /\ ~ Dirty(p)
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = CHOOSE x \in Values :
                        \A y \in Values : (x <= y) => (y \notin {view[p][q] : q \in 1..N})]
    /\ phase' = [phase EXCEPT ![p] = "ph2b"]
    /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recv>>

DecidePhase2(p, v) ==
    /\ phase[p] = "ph2w"
    /\ Cardinality({m \in recv[p] : m.type = "p2" /\ m.ev = v}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashedCount, sent, recv>>

Choose(p, v) ==
    /\ phase[p] = "choosing"
    /\ v \in {view[p][q] : q \in 1..N}
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ phase' = [phase EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashedCount, sent, recv>>

Transition(p) ==
    /\ phase[p] = "ph2w"
    /\ \A q \in 1..N : [type |-> "p2", val |-> prop[p], ev |-> estimate[p], sender |-> q] \in recv[p]
    /\ phase' = [phase EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, sent, recv>>

MoveToChoosing(p) ==
    /\ phase[p] = "ph2w"
    /\ ~Dirty(p)
    /\ ~\E v \in Values : Cardinality({m \in recv[p] : m.type = "p2" /\ m.ev = v}) >= N - T
    /\ phase' = [phase EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashedCount, sent, recv>>

Crash(p) ==
    /\ phase[p] \in {"ph1b", "ph1w", "ph2b", "ph2w"}
    /\ crashedCount < F
    /\ crashedCount' = crashedCount + 1
    /\ phase' = [phase EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in 1..N : BroadcastPH1(p)
    \/ \E p \in 1..N : BroadcastPH2(p)
    \/ \E p \in 1..N, m \in sent : ReceiveMsg(p, m)
    \/ \E p \in 1..N : ComputeEstimate(p)
    \/ \E p \in 1..N, v \in Values : DecidePhase2(p, v)
    \/ \E p \in 1..N :
           \/ Transition(p)
           \/ MoveToChoosing(p)
           \/ \E v \in Values : Choose(p, v)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_<<phase, view, prop, estimate, decision, crashedCount, sent, recv>>
    /\ UNCHANGED <<>> /\ UNCHANGED <<>>

TypeOK ==
    /\ phase \in [1..N -> Phases]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashedCount \in Nat
    /\ sent \subseteq [type : MsgTypes, val : Values, ev : Values \cup {Bottom}, sender : 1..N]
    /\ recv \in [1..N -> SUBSET [type : MsgTypes, val : Values, ev : Values \cup {Bottom}, sender : 1..N]]

Validity ==
    \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement ==
    \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
    \A p \in 1..N : <>(phase[p] \in {"crashed", "done"})

HasMax(v) == \E q \in 1..N : prop[q] = v
C1Condition == \E v \in Values : HasMax(v) /\ \A q \in 1..N : prop[q] <= v /\ Cardinality({q \in 1..N : prop[q] = v}) >= F + 1
ConditionalTermination == C1Condition => Termination

====