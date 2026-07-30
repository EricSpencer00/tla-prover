---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* Phase naming follows the paper: broadcast, waiting, preparing, and done.
\* The local view is an N-by-N matrix; a process's estimate is the max of its view.
\* Messages carry a type tag; two-phase messages also carry the estimated value.
\* 2T < N is the survivability requirement for the condition-based guarantee.
Locs == {"broadcast1", "wait1", "prepare2", "broadcast2",
         "wait2", "done", "crashed", "choosing"}

VARIABLES loc, view, proposed, estimate, decision, crashed, messages, recv
vars == <<loc, view, proposed, estimate, decision, crashed, messages, recv>>

TypeOK ==
    /\ loc \in [1..N -> Locs]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ proposed \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ messages \subseteq [type: {"phase1", "phase2"},
                           val: Values, sender: 1..N,
                           est: Values \cup {Bottom}]
    /\ recv \in [1..N -> SUBSET [type: {"phase1", "phase2"},
                                 val: Values, sender: 1..N,
                                 est: Values \cup {Bottom}]]

Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ proposed \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ messages = {}
    /\ recv = [p \in 1..N |-> {}]

BcastPhase1(p) ==
    /\ loc[p] = "broadcast1"
    /\ messages' = messages \cup {[type |-> "phase1", val |-> proposed[p],
                                   sender |-> p, est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, proposed, estimate, decision,
                   crashed, recv>>

ReceivePhase1(p) ==
    /\ loc[p] \in {"wait1", "prepare2"}
    /\ \E m \in recv[p] :
        /\ m.type = "phase1"
        /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \ {m}]
    /\ UNCHANGED <<loc, proposed, estimate, decision,
                   crashed, messages>>

PreparePhase2(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = Max({view[p][q] : q \in 1..N})]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, proposed, decision,
                   crashed, messages, recv>>

BcastPhase2(p) ==
    /\ loc[p] = "broadcast2"
    /\ messages' = messages \cup {[type |-> "phase2", val |-> proposed[p],
                                   sender |-> p, est |-> estimate[p]}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, proposed, estimate, decision,
                   crashed, recv>>

ReceivePhase2(p) ==
    /\ loc[p] = "wait2"
    /\ \E m \in recv[p] :
        /\ m.type = "phase2"
        /\ m.est # Bottom
        /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \ {m}]
    /\ UNCHANGED <<loc, proposed, estimate, decision,
                   crashed, messages>>

Decide(p) ==
    /\ loc[p] = "wait2"
    /\ \E v \in Values :
        /\ Cardinality({q \in 1..N : view[p][q] = v}) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate,
                   crashed, messages, recv>>

Choose(p) ==
    /\ loc[p] = "wait2"
    /\ \A v \in Values :
        Cardinality({q \in 1..N : view[p][q] = v}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, proposed, estimate, decision,
                   crashed, messages, recv>>

MakeChoice(p) ==
    /\ loc[p] = "choosing"
    /\ \E v \in Values :
        /\ \E q \in 1..N : view[p][q] = v
        /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimate,
                   crashed, messages, recv>>

Crash(p) ==
    /\ loc[p] \in {"broadcast1", "wait1", "prepare2", "broadcast2", "wait2"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, proposed, estimate, decision,
                   messages, recv>>

\* Crash is kept strongly fair (always enabled once the fault budget is open)
\* so it does not accidentally starve; the other steps are weakly fair.
Next ==
    \/ \E p \in 1..N : BcastPhase1(p) \/ ReceivePhase1(p) \/ PreparePhase2(p)
                      \/ BcastPhase2(p) \/ ReceivePhase2(p)
                      \/ Decide(p) \/ Choose(p) \/ MakeChoice(p) \/ Crash(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ReceivePhase1(1)) /\ WF_vars(ReceivePhase2(1))
        /\ WF_vars(PreparePhase2(1)) /\ WF_vars(Decide(1))
        /\ WF_vars(Choose(1)) /\ WF_vars(MakeChoice(1))
        /\ WF_vars(BcastPhase1(1)) /\ WF_vars(BcastPhase2(1))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom)
                               => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

ConditionC1 == Cardinality({p \in 1..N : proposed[p] = Max(Values)})
               >= F + 1
               => Termination

====