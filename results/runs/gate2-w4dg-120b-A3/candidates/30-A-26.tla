---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ 2 * T < N
       /\ F \in Nat /\ F <= T
       /\ Bottom \notin Values

VARIABLES
    loc, view, prop, est, decision, crashed, sent, rcvd

vars == <<loc, view, prop, est, decision, crashed, sent, rcvd>>

Locations ==
    {"phase1bcast", "phase1wait", "preparing", "phase2bcast",
     "phase2wait", "done", "crashed", "choosing"}

Phases == {"phase1", "phase2"}

TypeOK ==
    /\ loc \in [1..N -> Locations]
    /\ view \in [1..N -> 1..N -> Values \cup {Bottom}]
    /\ prop \in [1..N -> Values]
    /\ est \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ sent \in SUBSET [kind: Phases, val: Values, est: Values \cup {Bottom}, from: 1..N]
    /\ rcvd \in [1..N -> SUBSET [kind: Phases, val: Values, est: Values \cup {Bottom}, from: 1..N]]

Init ==
    /\ loc = [i \in 1..N |-> "phase1bcast"]
    /\ view = [i \in 1..N, j \in 1..N |-> Bottom]
    /\ prop \in [1..N -> Values]
    /\ est = [i \in 1..N |-> Bottom]
    /\ decision = [i \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ rcvd = [i \in 1..N |-> {}]

MaxInView(i) ==
    LET vals == {view[i][j] : j \in 1..N} \ {Bottom}
    IN IF vals = {} THEN Bottom ELSE CHOOSE v \in vals : \A w \in vals : w <= v

BroadcastPhase1(i) ==
    /\ loc[i] = "phase1bcast"
    /\ sent' = sent \cup {[kind |-> "phase1", val |-> prop[i], est |-> Bottom, from |-> i]}
    /\ loc' = [loc EXCEPT ![i] = "phase1wait"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceivePhase1(i) ==
    /\ loc[i] = "phase1wait"
    /\ \E m \in sent :
         /\ m.kind = "phase1"
         /\ view[i][m.from] = Bottom
         /\ view' = [view EXCEPT ![i][m.from] = m.val]
         /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

TransitionPhase1(i) ==
    /\ loc[i] = "phase1wait"
    /\ Cardinality({m \in rcvd[i] : m.kind = "phase1"}) >= N - T
    /\ est' = [est EXCEPT ![i] = MaxInView(i)]
    /\ loc' = [loc EXCEPT ![i] = "phase2bcast"]
    /\ UNCHANGED <<view, prop, decision, crashed, sent, rcvd>>

BroadcastPhase2(i) ==
    /\ loc[i] = "phase2bcast"
    /\ sent' = sent \cup {[kind |-> "phase2", val |-> prop[i], est |-> est[i], from |-> i]}
    /\ loc' = [loc EXCEPT ![i] = "phase2wait"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, rcvd>>

ReceivePhase2(i) ==
    /\ loc[i] = "phase2wait"
    /\ \E m \in sent :
         /\ m.kind = "phase2"
         /\ view[i][m.from] = Bottom
         /\ view' = [view EXCEPT ![i][m.from] = m.est]
         /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

DecideByThreshold(i) ==
    /\ loc[i] = "phase2wait"
    /\ \E v \in Values :
         /\ Cardinality({m \in rcvd[i] : m.kind = "phase2" /\ m.est = v}) >= N - T
         /\ decision' = [decision EXCEPT ![i] = v]
    /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Choose(i) ==
    /\ loc[i] = "phase2wait"
    /\ \A m \in rcvd[i] : m.kind = "phase2"
    /\ Cardinality({m.from : m \in rcvd[i]}) = N
    /\ loc' = [loc EXCEPT ![i] = "choosing"]
    /\ UNCHANGED <<view, prop, est, decision, crashed, sent, rcvd>>

DeterministicChoice(i) ==
    /\ loc[i] = "choosing"
    /\ decision' = [decision EXCEPT ![i] = MaxInView(i)]
    /\ loc' = [loc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Crash(i) ==
    /\ loc[i] \in Locations \ {"crashed"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![i] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, est, decision, sent, rcvd>>

Next ==
    \/ \E i \in 1..N : BroadcastPhase1(i) \/ ReceivePhase1(i) \/ TransitionPhase1(i)
                        \/ BroadcastPhase2(i) \/ ReceivePhase2(i) \/ DecideByThreshold(i)
                        \/ Choose(i) \/ DeterministicChoice(i) \/ Crash(i)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E i \in 1..N : ReceivePhase1(i))
    /\ WF_vars(\E i \in 1..N : ReceivePhase2(i))
    /\ WF_vars(\E i \in 1..N : TransitionPhase1(i))
    /\ WF_vars(\E i \in 1..N : Choose(i))
    /\ WF_vars(\E i \in 1..N : DeterministicChoice(i))

Validity == \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : prop[j] = decision[i]

Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

ConditionC1 == Cardinality({i \in 1..N : prop[i] = CHOOSE x \in Values : \A y \in Values : y <= x}) >= F + 1

====