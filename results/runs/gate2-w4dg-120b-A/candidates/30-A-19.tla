---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N > 0 /\ T >= 0 /\ F >= 0 /\ 2 * T < N
ASSUME Bottom \notin Values

\* Action labels: the control variable holds a label for each phase; the
\* label set is also used to name the precondition of each action.
Locations == {
  "broadcast1", "wait1", "prepare", "broadcast2", "wait2",
  "done", "crashed", "choosing"
}

\* Each process's local view of every other process's proposed value.
Views == [N -> [N -> Values \cup {Bottom}]]

Msgs == [type: {"phase1", "phase2"}, sender: 1..N, value: Values, extra: Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashedCount, sent, recv

vars == <<loc, view, prop, est, decision, crashedCount, sent, recv>>

TypeOK ==
  /\ loc \in [N -> Locations]
  /\ view \in Views
  /\ prop \in [N -> Values]
  /\ est \in [N -> Values \cup {Bottom}]
  /\ decision \in [N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> "broadcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", sender |-> p, value |-> prop[p], extra |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

\* Receivers accept only messages that match the phase they are waiting for.
Receive(p, m) ==
  /\ loc[p] \in {"wait1", "wait2"}
  /\ m \in sent
  /\ m.type = loc[p]
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashedCount, sent>>

Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values : \A y \in Values : (\A q \in 1..N : view[p][q] = x => y \in Values) => x >= y]
  /\ loc' = [loc EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, prop, decision, crashedCount, sent, recv>>

Broadcast2(p) ==
  /\ loc[p] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", sender |-> p, value |-> prop[p], extra |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, est, decision, crashedCount, recv>>

Decide(p, v) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.extra = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

Choose(p, v) ==
  /\ loc[p] = "wait2"
  /\ \A q \in 1..N : view[p][q] # Bottom
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, recv>>

\* Deterministic tie-breaking: the chooser commits the smallest value in view.
Commit(p) ==
  /\ loc[p] = "choosing"
  /\ decision[p] > Bottom
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, decision, crashedCount, sent, recv>>

\* Once a process is done the model lets it sit there; elsewhere it may crash.
Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {"crashed", "done"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Crash(p) \/ Commit(p)
  \/ \E p \in 1..N, v \in Values : Decide(p, v) \/ Choose(p, v)
  \/ \E p \in 1..N, m \in Msgs : Receive(p, m)

Spec == Init /\ [][Next]_vars
        /\ \A p \in 1..N : WF_vars(Broadcast1(p))
        /\ \A p \in 1..N : WF_vars(Receive(p, [type |-> "phase1", sender |-> 1, value |-> CHOOSE v \in Values : TRUE, extra |-> Bottom]))
        /\ \A p \in 1..N : WF_vars(Prepare(p))
        /\ \A p \in 1..N : WF_vars(Broadcast2(p))
        /\ \A p \in 1..N : WF_vars(Decide(p, CHOOSE v \in Values : TRUE))
        /\ \A p \in 1..N : WF_vars(Choose(p, CHOOSE v \in Values : TRUE))
        /\ \A p \in 1..N : WF_vars(Commit(p))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

ConditionC1 == \A p \in 1..N : prop[p] = CHOOSE v \in Values : \A q \in 1..N : v >= prop[q] => \E r \in 1..N : prop[r] = v /\ Cardinality({r \in 1..N : prop[r] = v}) >= F + 1 => <>(\A q \in 1..N : loc[q] \in {"done", "crashed"})

====