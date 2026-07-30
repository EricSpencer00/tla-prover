---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 and phase-2 message tags; a phase-2 message also carries an
\* estimated value, which makes it distinct from a phase-1 message.
MessageTags == {"phase1", "phase2"}
Phases == {"phase1", "phase2"}

VARIABLES loc, view, prop, estimate, decision, crashed, msgs, received

vars == <<loc, view, prop, estimate, decision, crashed, msgs, received>>

PhasesOf(p) == IF loc[p] \in {"broadcast1", "wait1"} THEN "phase1"
               ELSE IF loc[p] \in {"broadcast2", "wait2"} THEN "phase2"
               ELSE "none"

TypeOK ==
    /\ loc \in [1..N -> {"broadcast1", "wait1", "broadcast2", "wait2",
                         "done", "choose", "crashed"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ prop \in [1..N -> Values]
    /\ estimate \in [1..N -> Values \cup {Bottom}]
    /\ decision \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ msgs \subseteq [tag: MessageTags, val: Values, sender: 1..N,
                       estimate: Values \cup {Bottom}]
    /\ received \in [1..N -> SUBSET [tag: MessageTags, val: Values,
                                      sender: 1..N, estimate: Values \cup {Bottom}]]

Init ==
    /\ loc = [p \in 1..N |-> "broadcast1"]
    /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
    /\ prop \in [p \in 1..N -> Values]
    /\ estimate = [p \in 1..N |-> Bottom]
    /\ decision = [p \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ received = [p \in 1..N |-> {}]

Broadcast1(p) ==
    /\ loc[p] = "broadcast1"
    /\ msgs' = msgs \cup {[tag |-> "phase1", val |-> prop[p], sender |-> p,
                           estimate |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

Deliver(p, m) ==
    /\ loc[p] \in {"wait1", "wait2"}
    /\ m.tag = PhasesOf(p)
    /\ m \notin received[p]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ received' = [received EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, prop, estimate, decision, crashed, msgs>>

\* Once enough distinct phase-1 values are collected, p computes its
\* estimate as the maximum over its whole view (the crash condition C1
\* says this estimate is already the global max when the condition holds).
ComputeEstimate(p) ==
    /\ loc[p] = "wait1"
    /\ Cardinality({m.sender : m \in received[p] /\ m.tag = "phase1"}) >= N - T
    /\ estimate' = [estimate EXCEPT ![p] =
                      CHOOSE x \in Values :
                          \A q \in 1..N : view[p][q] \in Values => view[p][q] <= x]
    /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<view, prop, decision, crashed, msgs, received>>

Broadcast2(p) ==
    /\ loc[p] = "broadcast2"
    /\ msgs' = msgs \cup {[tag |-> "phase2", val |-> prop[p], sender |-> p,
                           estimate |-> estimate[p]]}
    /\ loc' = [loc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* A majority (N-T, a strict majority since 2T < N) agrees on the same
\* estimate: p decides it and terminates.
DecideFromAgree(p) ==
    /\ loc[p] = "wait2"
    /\ \E e \in Values :
         /\ Cardinality({m \in received[p] : m.tag = "phase2" /\ m.estimate = e})
              >= N - T
         /\ decision' = [decision EXCEPT ![p] = e]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, received>>

\* If nothing reaches the threshold, p picks a value still visible to it.
Choose(p) ==
    /\ loc[p] = "wait2"
    /\ \A e \in Values :
         Cardinality({m \in received[p] : m.tag = "phase2" /\ m.estimate = e})
              < N - T
    /\ loc' = [loc EXCEPT ![p] = "choose"]
    /\ UNCHANGED <<view, prop, estimate, decision, crashed, msgs, received>>

\* Deterministically selects a visible value rather than nondeterministic
\* choice, to avoid a spurious deadlock when no majority existed.
SelectVisible(p) ==
    /\ loc[p] = "choose"
    /\ \E e \in Values :
         /\ \E q \in 1..N : view[p][q] = e
         /\ decision' = [decision EXCEPT ![p] = e]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, prop, estimate, crashed, msgs, received>>

Crash(p) ==
    /\ loc[p] # "crashed"
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, prop, estimate, decision, msgs, received>>

AllDelivered == \A p \in 1..N : \A m \in msgs : Deliver(p, m)

Next ==
    \/ \E p \in 1..N : Broadcast1(p) \/ Broadcast2(p) \/ ComputeEstimate(p)
                       \/ DecideFromAgree(p) \/ Choose(p) \/ SelectVisible(p) \/ Crash(p)
    \/ AllDelivered

Spec == Init /\ [][Next]_vars /\ WF_vars(AllDelivered)

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N :
                 (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

====