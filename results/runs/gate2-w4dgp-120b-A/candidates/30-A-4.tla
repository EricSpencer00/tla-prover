---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

\* A value is conditionally decided when at least N-T processes (a quorum of
\* size N minus the tolerance bound) have echoed it.
\* Two phases: phase 1 disseminates proposals, phase 2 disseminates the
\* maximum estimate each process computed; a process may crash silently.

VARIABLES pc, view, prop, estimate, decision, crashed, sent, received

vars == <<pc, view, prop, estimate, decision, crashed, sent, received>>

Locs == {"bcast1", "wait1", "prepares", "bcast2", "wait2", "done", "crashed", "choosing"}

Msgs == [type : {"phase1", "phase2"}, val : Values, from : 0..(N-1), est : Values \cup {Bottom}]

TypeOK ==
  /\ pc \in [0..(N-1) -> Locs]
  /\ view \in [0..(N-1), 0..(N-1) -> Values \cup {Bottom}]
  /\ prop \in [0..(N-1) -> Values]
  /\ estimate \in [0..(N-1) -> Values \cup {Bottom}]
  /\ decision \in [0..(N-1) -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ received \in [0..(N-1) -> SUBSET Msgs]

Init ==
  /\ pc = [p \in 0..(N-1) |-> "bcast1"]
  /\ view = [p \in 0..(N-1), q \in 0..(N-1) |-> Bottom]
  /\ prop \in [0..(N-1) -> Values]
  /\ estimate = [p \in 0..(N-1) |-> Bottom]
  /\ decision = [p \in 0..(N-1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in 0..(N-1) |-> {}]

\* Phase 1 broadcast: every process puts its proposal into the wire.
Broadcast1(p) ==
  /\ pc[p] = "bcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], from |-> p, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* A process receives a phase-1 message and records the sender's value.
Deliver1(p, m) ==
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<pc, prop, estimate, decision, crashed, sent>>

\* Once a quorum of proposals is in view, the process computes its estimate
\* as the maximum of what it has heard.
Compute(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality({q \in 0..(N-1) : view[p][q] # Bottom}) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in {view[p][q] : q \in 0..(N-1)} : \A q \in 0..(N-1) : view[p][q] # Bottom => view[p][q] <= v]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, received>>

\* Phase 2 broadcast its proposal plus its computed estimate.
Broadcast2(p) ==
  /\ pc[p] = "bcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], from |-> p, est |-> estimate[p]]}
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* A process receives a phase-2 message and records its contents.
Deliver2(p, m) ==
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<pc, prop, estimate, decision, crashed, sent>>

\* If a quorum of phase-2 messages agree on an estimate, decide it and finish.
Decide(p) ==
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({q \in 0..(N-1) : \E m \in received[p] : m.type = "phase2" /\ m.from = q /\ m.est = v}) >= (N - T)
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* If no estimate has a quorum, the process deterministically picks any value
\* it has seen and decides it.
Choose(p) ==
  /\ pc[p] = "wait2"
  /\ \A v \in Values : Cardinality({q \in 0..(N-1) : \E m \in received[p] : m.type = "phase2" /\ m.from = q /\ m.est = v}) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, received>>

\* A crashed process stops; the crash budget is saturated at F.
Crash(p) ==
  /\ crashed < F
  /\ pc[p] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, received>>

Next ==
  \/ \E p \in 0..(N-1) : Broadcast1(p) \/ Compute(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 0..(N-1), m \in Msgs : Deliver1(p, m) \/ Deliver2(p, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Decide(0)) /\ WF_vars(Decide(1))
  /\ WF_vars(Choose(0)) /\ WF_vars(Choose(1))

\* Safety: a decision only ever reflects a value that someone actually proposed.
Validity == \A p \in 0..(N-1) : decision[p] # Bottom => \E q \in 0..(N-1) : decision[p] = prop[q]

\* Safety: if two processes both decide, they agree on the same value.
Agreement == \A p, q \in 0..(N-1) :
  (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Liveness: every process eventually either crashes or finishes with a decision.
Termination == \A p \in 0..(N-1) : <>(pc[p] \in {"crashed", "done"})

\* Conditional termination: if enough processes propose the global maximum, the
\* protocol cannot stall forever.
ConditionC1 == \E S \in SUBSET (0..(N-1)) :
  /\ Cardinality(S) >= (F + 1)
  /\ \A p \in S : prop[p] = (CHOOSE m \in Values : \A q \in Values : q <= m)
  /\ Termination

====