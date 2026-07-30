---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Control locations: broadcasting phase 1, phase-1 waiting, preparing
\* (computing estimate), broadcasting phase 2, phase-2 waiting, done,
\* crashed, and choosing (deterministic fallback).
Locations == {
    "bc1",    \* broadcasting phase 1
    "w1",     \* waiting for phase 1 messages
    "prep",   \* preparing, estimated value computed
    "bc2",    \* broadcasting phase 2
    "w2",     \* waiting for phase 2 messages
    "done",   \* has decided a value and finished
    "crashed",\* crashed
    "choose"  \* deterministic fallback after phase 2
}

AssumedOrder == Cardinality(Values) < Cardinality(Values) + 1

TypeOK ==
    /\ N \in Nat /\ N > 0
    /\ T \in Nat /\ 2 * T < N
    /\ F \in Nat /\ F <= T
    /\ Bottom \notin Values
    /\ Cardinality(Values) > 0
    /\ LEVEL == {0, 1, 2}
    /\ PROPOSED == [1..N -> Values]

VARIABLES loc, view, propose, estimate, decided, crashed, msgs, recv
vars == <<loc, view, propose, estimate, decided, crashed, msgs, recv>>

Init ==
    /\ loc = [p \in 1..N |-> "bc1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ propose \in PROPOSED
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decided = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ recv = [p \in 1..N |-> {}]

\* Phase 1 broadcast: each process sends its proposed value.
Broadcast1(p) ==
    /\ loc[p] = "bc1"
    /\ msgs' = msgs \cup {[type |-> 1, val |-> propose[p], from |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "w1"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

\* A process receives a message and updates its local view accordingly.
Receive(p, m) ==
    /\ loc[p] \in {"w1", "w2"}
    /\ m \in msgs
    /\ m.from \notin recv[p]
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.from}]
    /\ UNCHANGED <<loc, propose, estimate, decided, crashed, msgs>>

\* Once enough phase-1 messages are in, the estimate is the maximum view.
ComputeEstimate(p) ==
    /\ loc[p] = "w1"
    /\ Cardinality(recv[p]) >= N - T
    /\ \E v \in Values :
        /\ \A q \in 1..N : view[p][q] \in Values => v >= view[p][q]
        /\ estimate' = [estimate EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "bc2"]
    /\ UNCHANGED <<view, propose, decided, crashed, msgs, recv>>

\* Phase 2 broadcast: the process sends both its proposed and estimated values.
Broadcast2(p) ==
    /\ loc[p] = "bc2"
    /\ msgs' = msgs \cup {[type |-> 2, val |-> propose[p], from |-> p, est |-> estimate[p]]}
    /\ loc' = [loc EXCEPT ![p] = "w2"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

\* A process decides once enough phase-2 messages agree on an estimate.
Decide(p) ==
    /\ loc[p] = "w2"
    /\ \E v \in Values :
        /\ Cardinality({m \in msgs : m.type = 2 /\ m.est = v /\ m.from \in recv[p]}) >= N - T
        /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recv>>

\* If phase 2 collects everything with no N-T agreement, the process chooses.
StartChoosing(p) ==
    /\ loc[p] = "w2"
    /\ Cardinality(recv[p]) = N
    /\ \A v \in Values :
        Cardinality({m \in msgs : m.type = 2 /\ m.est = v /\ m.from \in recv[p]}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, propose, estimate, decided, crashed, msgs, recv>>

\* Deterministic fallback: the chooser selects any value it can see.
Choose(p) ==
    /\ loc[p] = "choose"
    /\ \E v \in Values :
        /\ \A q \in 1..N : view[p][q] \in Values => v >= view[p][q]
        /\ decided' = [decided EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recv>>

\* A process may crash, subject to the fault budget.
Crash(p) ==
    /\ loc[p] \notin {"crashed", "done"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, propose, estimate, decided, msgs, recv>>

Next ==
    \/ \E p \in 1..N : Broadcast1(p) \/ ComputeEstimate(p) \/ Broadcast2(p) \/ Decide(p)
                      \/ StartChoosing(p) \/ Choose(p) \/ Crash(p)
    \/ \E p \in 1..N, m \in msgs : Receive(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in msgs : Receive(p, m))
        /\ WF_vars(\E p \in 1..N : Broadcast1(p))
        /\ WF_vars(\E p \in 1..N : ComputeEstimate(p))
        /\ WF_vars(\E p \in 1..N : Broadcast2(p))
        /\ WF_vars(\E p \in 1..N : Decide(p))
        /\ WF_vars(\E p \in 1..N : StartChoosing(p))
        /\ WF_vars(\E p \in 1..N : Choose(p))

\* Bad: the agreed decision was never proposed. Good: it always traces back.
Validity == \A p \in 1..N : decided[p] # Bottom => decided[p] \in {propose[q] : q \in 1..N}

Agreement == \A p, q \in 1..N :
    (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Under Condition C1 (enough processes propose the max), termination is forced.
ConditionalTermination == (Cardinality({p \in 1..N : propose[p] = (CHOOSE x \in Values : \A y \in Values : y <= x)}) >= F + 1) ~> Termination
====