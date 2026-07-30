---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Locations describe the two-phase control flow plus the fault states.
Locations == {"ph1broad", "ph1wait", "prepare", "ph2broad", "ph2wait", "done",
              "crashed", "choose"}

Msgs == [type : {"ph1", "ph2"}, val : Values, snd : 1..N, est : Values \cup {Bottom}]
Views == [1..N -> Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decided, crashed, sent, rcvd
vars == <<loc, view, prop, est, decided, crashed, sent, rcvd>>

SendMe(m) == \A p \in 1..N : rcvd[p] = rcvd[p] \cup {m}

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> Views]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ rcvd \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> "ph1broad"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [p \in 1..N |-> {}]

\* Phase 1 broadcast: propose the process's own value.
BroadcastPh1(p) ==
  /\ loc[p] = "ph1broad"
  /\ loc' = [loc EXCEPT ![p] = "ph1wait"]
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], snd |-> p, est |-> Bottom]}
  /\ UNCHANGED <<view, prop, est, decided, crashed, rcvd>>

\* Phase 1 receive: update the local view with the sender's value.
RecvPh1(p, m) ==
  /\ loc[p] = "ph1wait"
  /\ m \in sent
  /\ m.type = "ph1"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p] = [view[p] EXCEPT ![m.snd] = m.val]]
  /\ SendMe(m)
  /\ UNCHANGED <<loc, prop, est, decided, crashed, sent, rcvd>>

\* Phase 1 transition: after enough distinct phase-1 values, estimate the max and move on.
Phase1Transition(p) ==
  /\ loc[p] = "ph1wait"
  /\ Cardinality({m \in rcvd[p] : m.type = "ph1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values :
                            \A q \in 1..N : view[p][q] = Bottom \/ x >= view[p][q]]
  /\ loc' = [loc EXCEPT ![p] = "ph2broad"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, rcvd>>

\* Phase 2 broadcast: carry both the proposed and estimated values.
BroadcastPh2(p) ==
  /\ loc[p] = "ph2broad"
  /\ loc' = [loc EXCEPT ![p] = "ph2wait"]
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], snd |-> p, est |-> est[p]]}
  /\ UNCHANGED <<view, prop, est, decided, crashed, rcvd>>

\* Phase 2 receive: only the current phase is observed.
RecvPh2(p, m) ==
  /\ loc[p] = "ph2wait"
  /\ m \in sent
  /\ m.type = "ph2"
  /\ view[p][m.snd] = Bottom
  /\ view' = [view EXCEPT ![p] = [view[p] EXCEPT ![m.snd] = m.est]]
  /\ SendMe(m)
  /\ UNCHANGED <<loc, prop, est, decided, crashed, sent, rcvd>>

\* Phase 2 transition: any estimated value reaching the quorum decides it.
Phase2Transition(p) ==
  /\ loc[p] = "ph2wait"
  /\ \E v \in Values :
        /\ Cardinality({m \in rcvd[p] : m.type = "ph2" /\ m.est = v}) >= N - T
        /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

\* Phase 2 fallback: if the quorum never forms on an estimate, pick something.
ChooseBacktrack(p) ==
  /\ loc[p] = "ph2wait"
  /\ \A q \in 1..N : view[p][q] # Bottom
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, sent, rcvd>>

Choose(p, v) ==
  /\ loc[p] = "choose"
  /\ v \in {view[p][q] : q \in 1..N}
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decided, sent, rcvd>>

Next ==
  \/ \E p \in 1..N : BroadcastPh1(p) \/ Phase1Transition(p) \/ BroadcastPh2(p) \/ Phase2Transition(p) \/ ChooseBacktrack(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in Msgs : RecvPh1(p, m) \/ RecvPh2(p, m)
  \/ \E p \in 1..N, v \in Values : Choose(p, v)

Fairness ==
  /\ \A p \in 1..N : TRUE
  /\ \A p \in 1..N : TRUE
  /\ \A p \in 1..N : TRUE
  /\ \A p \in 1..N : TRUE

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safe values were proposed; no two processes disagree.
Validity == \A p \in 1..N : decided[p] # Bottom => decided[p] \in {prop[q] : q \in 1..N}
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Terminate == \A p \in 1..N : loc[p] \in {"done", "crashed"}

MaxProp == CHOOSE x \in Values : \A p \in 1..N : x >= prop[p]
CondC1 == (Cardinality({p \in 1..N : prop[p] = MaxProp}) >= F + 1) ~> Terminate

Terminating =~> Terminate

====