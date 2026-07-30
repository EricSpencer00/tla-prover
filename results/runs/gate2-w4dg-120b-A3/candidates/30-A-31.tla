---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N, T, F, Values, Bottom

ASSUME /\ 2 * T < N
       /\ 0 <= F /\ F <= T
       /\ N > 0
       /\ Bottom \notin Values

VARIABLES
    loc, view, prop, est, decision, crashes, msgs, rcvd

vars == <<loc, view, prop, est, decision, crashes, msgs, rcvd>>

MsgTypes == {"phase1", "phase2"}

TypeOK ==
    /\ loc \in [1..N -> {"broadcast1", "wait1", "prepare", "broadcast2",
                         "wait2", "done", "crashed", "choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashes \in 0..F
    /\ msgs \subseteq [type: MsgTypes, val: Values, sender: 1..N,
                       est: Values \cup {Bottom}]
    /\ rcvd \in [1..N -> SUBSET [type: MsgTypes, val: Values, sender: 1..N,
                                  est: Values \cup {Bottom}]]

Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ est = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashes = 0
    /\ msgs = {}
    /\ rcvd = [p \in 1..N |-> {}]

Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ msgs' = msgs \cup {[type |-> "phase1", val |-> prop[p],
                           sender |-> p, est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, est, decision, crashes, rcvd>>

Receive1(p, m) ==
    /\ loc[p] = "wait1"
    /\ m.type = "phase1"
    /\ m \notin rcvd[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, crashes, msgs>>

ComputeEst(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ est' = [est EXCEPT ![p] =
                 CHOOSE v \in Values :
                    \E S \in SUBSET 1..N :
                       /\ Cardinality(S) = N - T
                       /\ \A q \in S : view[p][q] = v]
               ]
    /\ loc' = [loc EXCEPT ![p] = "prepare"]
    /\ UNCHANGED <<view, prop, decision, crashes, msgs, rcvd>>

Broadcast2(p) ==
    /\ loc[p] = "prepare"
    /\ msgs' = msgs \cup {[type |-> "phase2", val |-> prop[p],
                           sender |-> p, est |-> est[p]]}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, est, decision, crashes, rcvd>>

Receive2(p, m) ==
    /\ loc[p] = "wait2"
    /\ m.type = "phase2"
    /\ m \notin rcvd[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, crashes, msgs>>

Decide(p, v) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.est = v}) >= N - T
    /\ decision[p] = Bottom
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashes, msgs, rcvd>>

Choose(p, v) ==
    /\ loc[p] = "choose"
    /\ decision[p] = Bottom
    /\ v \in {view[p][q] : q \in 1..N}
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, est, crashes, msgs, rcvd>>

Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashes < F
    /\ crashes' = crashes + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, est, decision, msgs, rcvd>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p) \/ ComputeEst(p) \/ Broadcast2(p)
                         \/ Choose(p, CHOOSE v \in Values : TRUE)
    \/ \E p \in 1..N, m \in msgs : Receive1(p, m) \/ Receive2(p, m)
    \/ \E p \in 1..N, v \in Values : Decide(p, v)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in 1..N : WF_vars(Receive1(p, CHOOSE m \in msgs : TRUE))
        /\ \A p \in 1..N : WF_vars(Receive2(p, CHOOSE m \in msgs : TRUE))
        /\ \A p \in 1..N : WF_vars(ComputeEst(p) \/ Broadcast2(p))
        /\ \A p \in 1..N : WF_vars(Choose(p, CHOOSE v \in Values : TRUE))

Validity ==
    \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement ==
    \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom)
                        => decision[p] = decision[q]

Terminate == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

ConditionC1 ==
    (Cardinality({p \in 1..N : prop[p] = CHOOSE v \in Values : TRUE})
       >= F + 1) ~> Terminate

====