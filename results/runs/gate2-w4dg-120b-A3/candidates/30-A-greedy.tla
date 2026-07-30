---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 and phase-2 messages are distinguished by their type; phase-2
\* messages also carry the sender's estimated value.
Message == [type: {"phase1", "phase2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashed, sent, recv

vars == <<loc, view, prop, est, decision, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ recv \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* A process may crash at any point, provided the fault budget is not spent.
Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, recv>>

BroadcastPhase1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

\* A phase-1 message updates the receiver's view of the sender's proposed value.
ReceivePhase1(p, m) ==
  /\ loc[p] = "w1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Once enough phase-1 messages have been collected, the process computes its
\* estimate as the maximum of its view and moves to phase 2.
Prepare(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in recv[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values : \A y \in Values \cup {Bottom} :
                (\A q \in 1..N : view[p][q] = y => y <= x)]
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "b2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, recv>>

\* A phase-2 message updates the receiver's view of the sender's estimate.
ReceivePhase2(p, m) ==
  /\ loc[p] = "w2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.est]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Decision: the majority estimate is adopted once it reaches the N-T threshold.
Decide(p) ==
  /\ loc[p] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* If no estimate reaches the threshold, the process deterministically picks one
\* from its view and decides on it.
Choose(p) ==
  /\ loc[p] = "w2"
  /\ \A v \in Values : Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ \E v \in Values :
       /\ \E q \in 1..N : view[p][q] = v
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

Next ==
  \/ \E p \in 1..N : Crash(p) \/ BroadcastPhase1(p) \/ Prepare(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p)
  \/ \E p \in 1..N, m \in Message : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

\* Weak fairness on every action that can fire repeatedly.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase1(p, m))
  /\ WF_vars(\E p \in 1..N : Prepare(p))
  /\ WF_vars(\E p \in 1..N : BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1..N, m \in Message : ReceivePhase2(p, m))
  /\ WF_vars(\E p \in 1..N : Decide(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Condition C1: enough processes propose the global maximum to guarantee
\* termination (the condition the spec is named after).
ConditionalTermination ==
  (Cardinality({p \in 1..N : prop[p] = CHOOSE x \in Values : \A y \in Values : y <= x}) >= F + 1) ~> Termination

====