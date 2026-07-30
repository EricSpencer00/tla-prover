---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Locations == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2",
              "done", "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}

VARIABLES loc, view, prop, est, decision, crashed, sent, recv

vars == <<loc, view, prop, est, decision, crashed, sent, recv>>

Msgs == [type: MsgTypes, val: Values, src: 1..N, est: Values \cup {Bottom}]

MaxV(t) == CHOOSE x \in Values : \A y \in Values : y <= x

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> "broadcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], src |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.src] = Bottom
  /\ view' = [view EXCEPT ![p][m.src] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

Estimate(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({m \in recv[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxV({view[p][q] : q \in 1..N} \cup {prop[p]})]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], src |-> p,
                         est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[p][m.src] = Bottom
  /\ view' = [view EXCEPT ![p][m.src] = m.est]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

Decide(p, v) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Choose(p, v) ==
  /\ loc[p] = "choose"
  /\ v \in {view[p][q] : q \in 1..N}
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

MoveChoose(p) ==
  /\ loc[p] = "wait2"
  /\ \A m \in recv[p] : m.type = "phase2"
  /\ \A v \in Values : Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, recv>>

Crash(p) ==
  /\ crashed < F
  /\ loc[p] \notin {"done", "crashed"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p)
  \/ \E p \in 1..N, m \in Msgs : Receive1(p, m)
  \/ \E p \in 1..N : Estimate(p)
  \/ \E p \in 1..N : Broadcast2(p)
  \/ \E p \in 1..N, m \in Msgs : Receive2(p, m)
  \/ \E p \in 1..N, v \in Values : Decide(p, v)
  \/ \E p \in 1..N, v \in Values : Choose(p, v)
  \/ \E p \in 1..N : MoveChoose(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars

Validity ==
  \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

Agreement ==
  \A p, q \in 1..N :
    (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  \A p \in 1..N : (loc[p] = "done" \/ loc[p] = "crashed")

C1 ==
  \A p \in 1..N :
    (loc[p] \in {"done", "crashed"} \/ decision[p] # Bottom)

\* Weak fairness on the phase-1, phase-2, and deterministic choosing paths.
Fairness ==
  /\ \A p \in 1..N : WF_vars(Broadcast1(p))
  /\ \A p \in 1..N : WF_vars(Estimate(p))
  /\ \A p \in 1..N : WF_vars(Broadcast2(p))
  /\ \A p \in 1..N : WF_vars(Decide(p, MaxV(Values)))
  /\ \A p \in 1..N : WF_vars(Choose(p, MaxV(Values)))
  /\ \A p \in 1..N : WF_vars(Crash(p))

====