---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ T >= F /\ Bottom \notin Values

VARIABLES loc, view, prop, estimate, decision, crashed, sent, recv

\* The protocol uses two broadcast phases (phase 1, phase 2) before each process
\* computes an estimate and either decides on a majority estimate or falls back
\* to a deterministic choice from its local view. Messages carry the sender
\* identity.
Message == [type : {1, 2}, val : Values, est : Values \cup {Bottom}, from : 1..N]

Rcvd(p, ph) == {m \in recv[p] : m.type = ph}

MaxV(S) == LET f[T \in SUBSET S] == IF T = {} THEN Bottom ELSE LET x == CHOOSE y \in T : TRUE IN IF S \cup {x} = S THEN f[T \ {x}] ELSE IF f[T \ {x}] = Bottom THEN x ELSE IF f[T \ {x}] > x THEN f[T \ {x}] ELSE x IN f[S]

TypeOK ==
    /\ loc \in [1..N -> {"phase1", "phase2", "preparing", "phase2wait", "done", "crashed", "choose"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..F
    /\ sent \subseteq Message
    /\ recv \in [1..N -> SUBSET Message]

Init ==
    /\ loc = [p \in 1..N |-> "phase1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

\* Phase 1: each process broadcasts its proposed value.
BroadcastPhase1(p) ==
    /\ loc[p] = "phase1"
    /\ sent' = sent \cup {[type |-> 1, val |-> prop[p], est |-> Bottom, from |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "phase2"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* Phase 1: a process receives a broadcast, filling its view.
ReceivePhase1(p, m) ==
    /\ loc[p] = "phase2"
    /\ m \in sent /\ m.type = 1
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* Phase 1: once enough distinct phase-1 messages are in the view, compute the
\* maximum estimate and go to phase 2 broadcast.
Prepare(p) ==
    /\ loc[p] = "phase2"
    /\ Cardinality(Rcvd(p, 1)) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] = MaxV({view[p][q] : q \in 1..N /\ view[p][q] # Bottom})]
    /\ loc' = [loc EXCEPT ![p] = "preparing"]
    /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

\* Phase 2: each process broadcasts its proposed value together with its estimate.
BroadcastPhase2(p) ==
    /\ loc[p] = "preparing"
    /\ sent' = sent \cup {[type |-> 2, val |-> prop[p], est |-> estimate[p], from |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "phase2wait"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* Phase 2: a process receives a broadcast and updates its view.
ReceivePhase2(p, m) ==
    /\ loc[p] = "phase2wait"
    /\ m \in sent /\ m.type = 2
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* Phase 2: if a majority (N - T) agree on an estimate, decide it.
Decide(p) ==
    /\ loc[p] = "phase2wait"
    /\ \E c \in Values :
        Cardinality({m \in recv[p] : m.type = 2 /\ m.est = c}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = c]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* Phase 2: if no estimate reaches the majority, the process deterministically
\* chooses a value from its view and decides it.
ChooseValue(p) ==
    /\ loc[p] = "phase2wait"
    /\ \A c \in Values :
        Cardinality({m \in recv[p] : m.type = 2 /\ m.est = c}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, recv>>

\* The fallback deterministic choice.
DecideChosen(p) ==
    /\ loc[p] = "choose"
    /\ \E c \in Values : c \in {view[p][q] : q \in 1..N /\ view[p][q] # Bottom}
    /\ decision' = [decision EXCEPT ![p] = CHOOSE c \in Values :
                        c \in {view[p][q] : q \in 1..N /\ view[p][q] # Bottom}]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {"done", "crashed"}
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
    \/ \E p \in 1..N : BroadcastPhase1(p) \/ Prepare(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ ChooseValue(p) \/ DecideChosen(p) \/ Crash(p)
    \/ \E p \in 1..N : \E m \in Message : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Spec ==
    /\ Init /\ [][Next]_<<loc, view, prop, estimate, decision, crashed, sent, recv>>
    /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
    /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase1(p, m))
    /\ WF_vars(\E p \in 1..N : Prepare(p))
    /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
    /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase2(p, m))
    /\ WF_vars(\E p \in 1..N : Decide(p))
    /\ WF_vars(\E p \in 1..N : ChooseValue(p))
    /\ WF_vars(\E p \in 1..N : DecideChosen(p))

Validity == \A p \in 1..N : decision[p] # Bottom => \E q \in 1..N : prop[q] = decision[p]

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

ConditionC1 == Cardinality({p \in 1..N : prop[p] = MaxV({prop[q] : q \in 1..N})}) >= F + 1

ConditionalTermination == ConditionC1 ~> Termination

====