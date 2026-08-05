---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, estimate, decision, crashed, sent, recv
vars == <<loc, view, prop, estimate, decision, crashed, sent, recv>>

RECURSIVE SetOf(_, _)
SetOf(f, S) == {f[x] : x \in S}

\* The per-process local view is a full N-by-N matrix so that every received
\* value, whatever phase it arrives in, is preserved and available to the
\* maximum-compute step that follows phase 1.

Messages == [type : {"phase1", "phase2"}, value : Values, sender : 1..N]

MaxOf(f, S) ==
    LET g[x \in S] == f[x] IN
    IF \A x \in S : g[x] = Bottom
    THEN Bottom
    ELSE LET m == CHOOSE y \in S : \A z \in S : g[y] >= g[z] IN g[m]

TypeOK ==
    /\ loc \in [1..N -> {"broadcast1", "wait1", "prepare", "broadcast2",
                         "wait2", "done", "crashed", "choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Messages
    /\ recv \subseteq Messages

Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = {}

BroadcastPhase1(p) ==
    /\ loc[p] = "broadcast1"
    /\ sent' = sent \cup {[type |-> "phase1", value |-> prop[p], sender |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

ReceivePhase1(p, m) ==
    /\ m.type = "phase1"
    /\ loc[p] = "wait1"
    /\ m \in sent
    /\ m \notin recv
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = recv \cup {m}
    /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({m \in recv : m.type = "phase1" /\ m.sender # p}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxOf(view, {q \in 1..N : view[p][q] # Bottom})]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, crashed, sent, recv, decision>>

BroadcastPhase2(p) ==
    /\ loc[p] = "broadcast2"
    /\ sent' = sent \cup {[type |-> "phase2", value |-> prop[p], sender |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

ReceivePhase2(p, m) ==
    /\ m.type = "phase2"
    /\ loc[p] = "wait2"
    /\ m \in sent
    /\ m \notin recv
    /\ view' = [view EXCEPT ![p][m.sender] = m.value]
    /\ recv' = recv \cup {m}
    /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ Cardinality({m \in recv : m.type = "phase2" /\ view[p][m.sender] = estimate[p]}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = estimate[p]]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Choose(p) ==
    /\ loc[p] = "wait2"
    /\ \A m \in recv : m.type = "phase2" => m.sender \in 1..N
    /\ Cardinality({m \in recv : m.type = "phase2"}) = N
    /\ Card({m \in recv : m.type = "phase2" /\ view[p][m.sender] = estimate[p]}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, recv>>

Select(p) ==
    /\ loc[p] = "choose"
    /\ SetOf(view[p], 1..N) # {Bottom}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE v \in SetOf(view[p], 1..N) : v # Bottom]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
    \E p \in 1..N :
        \/ BroadcastPhase1(p)
        \/ BroadcastPhase2(p)
        \/ ComputeEstimate(p)
        \/ Decision(p)
        \/ Choose(p)
        \/ Select(p)
        \/ Crash(p)
        \/ \E m \in Messages :
            \/ ReceivePhase1(p, m)
            \/ ReceivePhase2(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
        /\ WF_vars(\E p \in 1..N : ReceivePhase1(p, CHOOSE m \in Messages : m.type = "phase1"))
        /\ WF_vars(\E p \in 1..N : ComputeEstimate(p))
        /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
        /\ WF_vars(\E p \in 1..N : ReceivePhase2(p, CHOOSE m \in Messages : m.type = "phase2"))
        /\ WF_vars(\E p \in 1..N : Decide(p))
        /\ WF_vars(\E p \in 1..N : Choose(p))
        /\ WF_vars(\E p \in 1..N : Select(p))

Validity ==
    \A p \in 1..N : decision[p] # Bottom => decision[p] \in SetOf(prop, 1..N)

Agreement ==
    \A p, q \in 1..N :
        (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
    \A p \in 1..N : (loc[p] = "crashed" \/ loc[p] = "done")

ConditionC1 ==
    \A p \in 1..N : (loc[p] = "crashed" \/ loc[p] = "done")
    \/ (\E m \in Values : (\A q \in 1..N : prop[q] = m \/ m = MaxOf(prop, 1..N))
        /\ Cardinality({q \in 1..N : prop[q] = m}) > F)

====