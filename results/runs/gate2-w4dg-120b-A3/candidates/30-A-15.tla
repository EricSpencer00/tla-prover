---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME T >= F /\ 2 * T < N /\ Bottom \notin Values /\ N > 0

VARIABLES loc, view, prop, estimate, decided, crashed, msgs, recvd

TypeOK ==
    /\ loc \in [1..N -> {"phase1bcast", "phase1wait", "preparing",
                         "phase2bcast", "phase2wait", "done",
                         "crashed", "choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decided \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ msgs \subseteq [type : {"phase1", "phase2"},
                       val : Values, sender : 1..N,
                       maxval : Values \cup {Bottom}]
    /\ recvd \in [1..N -> SUBSET [type : {"phase1", "phase2"},
                                 val : Values, sender : 1..N,
                                 maxval : Values \cup {Bottom}]]

Init ==
    /\ loc = [p \in 1..N |-> "phase1bcast"]
    /\ view = [q \in 1..N |-> [p \in 1..N |-> Bottom]]
    /\ \E f \in [1..N -> Values] : prop = f
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ recvd = [p \in 1..N |-> {}]

BcastPhase1(p) ==
    /\ loc[p] = "phase1bcast"
    /\ msgs' = msgs \cup {[type |-> "phase1", val |-> prop[p],
                           sender |-> p, maxval |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "phase1wait"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvd>>

Receive(p, m) ==
    /\ loc[p] \in {"phase1wait", "phase2wait"}
    /\ m \in msgs
    /\ m.type = (IF loc[p] = "phase1wait" THEN "phase1" ELSE "phase2")
    /\ m.sender \notin {q.sender : q \in recvd[p]}
    /\ m.val \in Values
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decided, crashed, msgs>>

MaxInView(p) ==
    LET vals == {view[p][q] : q \in 1..N} \ {Bottom}
    IN IF vals = {} THEN Bottom ELSE CHOOSE x \in vals : \A y \in vals : y <= x

Prepare(p) ==
    /\ loc[p] = "phase1wait"
    /\ Cardinality({q.sender : q \in recvd[p]}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxInView(p)]
    /\ loc' = [loc EXCEPT ![p] = "phase2bcast"]
    /\ UNCHANGED <<view, prop, decided, crashed, msgs, recvd>>

BcastPhase2(p) ==
    /\ loc[p] = "phase2bcast"
    /\ msgs' = msgs \cup {[type |-> "phase2", val |-> prop[p],
                           sender |-> p, maxval |-> estimate[p]]}
    /\ loc' = [loc EXCEPT ![p] = "phase2wait"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, recvd>>

Decide(p, v) ==
    /\ loc[p] = "phase2wait"
    /\ v \in Values
    /\ Cardinality({q.sender : q \in recvd[p] /\ q.type = "phase2"
                                   /\ q.maxval = v}) >= N - T
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, recvd>>

Choose(p) ==
    /\ loc[p] = "phase2wait"
    /\ {q.sender : q \in recvd[p] /\ q.type = "phase2"} = 1..N
    /\ \A v \in Values :
        Cardinality({q.sender : q \in recvd[p] /\ q.type = "phase2"
                                   /\ q.maxval = v}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, prop, estimate, decided, crashed, msgs, recvd>>

Select(p, v) ==
    /\ loc[p] = "choose"
    /\ v \in {view[p][q] : q \in 1..N} \ {Bottom}
    /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, recvd>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"crashed", "done"}
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, estimate, decided, msgs, recvd>>

Next ==
    \/ \E p \in 1..N : BcastPhase1(p) \/ Prepare(p) \/ BcastPhase2(p)
                        \/ Choose(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in msgs : Receive(p, m)
    \/ \E p \in 1..N, v \in Values : Decide(p, v) \/ Select(p, v)

Spec == Init /\ [][Next]_<<loc, view, prop, estimate, decided,
                                  crashed, msgs, recvd>>

Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N :
                                   decided[p] = prop[q]

Agreement == \A a, b \in 1..N : (decided[a] # Bottom /\ decided[b] # Bottom)
                                   => decided[a] = decided[b]

Terminate == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

C1 == \E S \in SUBSET 1..N : Cardinality(S) >= F + 1
                              /\ \A p \in S : prop[p] = MaxInView("phase2wait")

ConditionalTerminate == C1 ~> Terminate

====