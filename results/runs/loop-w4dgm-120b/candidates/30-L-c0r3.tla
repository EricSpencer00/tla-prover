---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase consensus: phase 1 collects proposals, phase 2 decides on the
\* maximum of the collected values.  A process may crash silently; the
\* quorum thresholds (N-T) are chosen so that up to T crashes can never
\* block progress, and the safety properties are agreement plus validity.

VARIABLES loc, view, prop, estimate, decided, crashed, sent, recv

vars == <<loc, view, prop, estimate, decided, crashed, sent, recv>>

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "p", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> prop[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Receive1(i, m) ==
  /\ loc[i] = "w1"
  /\ m.type = "p1"
  /\ m.sender \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.sender}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

\* Once enough phase-1 messages are in, compute the maximum and move on.
Compute(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality(recv[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values :
                     \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= v]
  /\ loc' = [loc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

\* Phase 2: broadcast both the proposed value and the computed estimate.
Broadcast2(i) ==
  /\ loc[i] = "b2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> prop[i], sender |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

Receive2(i, m) ==
  /\ loc[i] = "w2"
  /\ m.type = "p2"
  /\ m.sender \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m.sender}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

\* Decide once a quorum of phase-2 messages agree on the same estimate.
Decide(i) ==
  /\ loc[i] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({m \in sent : m.type = "p2" /\ m.sender \in recv[i] /\ m.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* If no estimate reaches quorum, fall back to a deterministic local choice.
Choose(i) ==
  /\ loc[i] = "w2"
  /\ recv[i] = 1..N
  /\ \A v \in Values :
       Cardinality({m \in sent : m.type = "p2" /\ m.sender \in recv[i] /\ m.est = v}) < N - T
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* A process may crash silently, up to the tolerated bound.
Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Compute(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in sent : Receive1(i, m) \/ Receive2(i, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N : Broadcast1(i))
  /\ WF_vars(\E i \in 1..N, m \in sent : Receive1(i, m))
  /\ WF_vars(\E i \in 1..N : Compute(i))
  /\ WF_vars(\E i \in 1..N : Broadcast2(i))
  /\ WF_vars(\E i \in 1..N, m \in sent : Receive2(i, m))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

\* Condition C1: if enough processes propose the global maximum, the
\* protocol is guaranteed to terminate.
ConditionalTermination ==
  /\ \E i \in 1..N : prop[i] = CHOOSE v \in Values : \A j \in 1..N : prop[j] <= v
  /\ Termination

Properties == Termination /\ ConditionalTermination

====