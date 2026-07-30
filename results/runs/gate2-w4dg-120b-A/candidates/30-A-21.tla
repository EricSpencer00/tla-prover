---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase, maximum-proposal consensus with crash faults, modeled on
\* Mostefaoui et al. 2003, C1.  Phase-1 messages share the proposed value;
\* phase-2 messages also carry the estimated maximum.  A process decides
\* the majority estimated value once enough phase-2 messages agree.

VARIABLES loc, view, prop, estimate, decided, crashed, msgs, rcv

TypeOK ==
  /\ loc \in [1..N -> {"bcast1", "wait1", "prepared", "bcast2", "wait2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \in SUBSET [type: {"phase1", "phase2"}, v: Values, sender: 1..N, est: Values \cup {Bottom}]
  /\ rcv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [i \in 1..N |-> "bcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ rcv = [i \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(i) ==
  /\ loc[i] = "bcast1"
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ msgs' = msgs \cup {[type |-> "phase1", v |-> prop[i], sender |-> i, est |-> Bottom]}
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, rcv>>

\* A process absorbs any in-flight message (phase match via loc).
Receive(i, m) ==
  /\ loc[i] \in {"wait1", "wait2"}
  /\ m \in msgs
  /\ m.sender \notin rcv[i]
  /\ (loc[i] = "wait1" => m.type = "phase1") /\ (loc[i] = "wait2" => m.type = "phase2")
  /\ view' = [view EXCEPT ![i][m.sender] = m.v]
  /\ estimate' = [estimate EXCEPT ![i] = IF loc[i] = "wait1" THEN m.est ELSE estimate[i]]
  /\ rcv' = [rcv EXCEPT ![i] = @ \cup {m.sender}]
  /\ UNCHANGED <<loc, prop, decided, crashed, msgs>>

\* Phase-1 waiting: once enough distinct phase-1 messages are held, compute
\* the local maximum estimate and move to broadcasting phase 2.
Prepare(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality(rcv[i]) >= N - T
  /\ \E v \in Values : v >= view[i][j] /\ v >= prop[i] /\ \A j \in 1..N : v >= view[i][j]
  /\ estimate' = [estimate EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "bcast2"]
  /\ UNCHANGED <<view, prop, decided, crashed, msgs, rcv>>

\* Phase 2: broadcast both the proposed value and the local estimate.
Broadcast2(i) ==
  /\ loc[i] = "bcast2"
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ msgs' = msgs \cup {[type |-> "phase2", v |-> prop[i], sender |-> i, est |-> estimate[i]]}
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, rcv>>

\* A waiting process decides the majority phase-2 estimate once enough agree.
Decide(i) ==
  /\ loc[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({m \in msgs : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcv>>

\* Without a majority, a process deterministically picks any observed value.
Choose(i) ==
  /\ loc[i] = "wait2"
  /\ \A v \in Values : Cardinality({m \in msgs : m.type = "phase2" /\ m.est = v}) < N - T
  /\ \E v \in Values : \E j \in 1..N : view[i][j] = v
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcv>>

\* A process crashes, bounded by the tolerated fault count.
Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, msgs, rcv>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Broadcast2(i) \/ Prepare(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in msgs : Receive(i, m)

vars == <<loc, view, prop, estimate, decided, crashed, msgs, rcv>>

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in msgs : Receive(i, m))
  /\ WF_vars(\E i \in 1..N : Broadcast1(i))
  /\ WF_vars(\E i \in 1..N : Broadcast2(i))
  /\ WF_vars(\E i \in 1..N : Prepare(i))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

ConditionalTermination == (\E i \in 1..N : prop[i] = (CHOOSE m \in Values : \A k \in Values : k <= m))
  => <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

====