---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol has two phases; a process may crash silently at any time.
\* Phase 1: broadcast a proposed value, collect enough phase-1 messages, and
\* compute an estimated value as the maximum seen. Phase 2: broadcast both
\* the proposed and estimated values, then decide once enough phase-2 messages
\* agree on the same estimated value. If the condition C1 holds (enough
\* processes propose the global maximum), the protocol is guaranteed to
\* terminate; otherwise a process may fall back to choosing from its view.

VARIABLES loc, view, prop, estimate, decided, crashed, sent, recv

Locs == {"bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choosing"}

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values, sender: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [p \in 1..N |-> "bcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(p) ==
  /\ loc[p] = "bcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

\* A process receives a phase-1 message and records the sender's value.
Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m.type = "phase1"
  /\ m.sender \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

\* Once enough phase-1 messages are collected, compute the estimated value.
Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                     \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= v]
  /\ loc' = "prepare"
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

\* Phase 2: broadcast both the proposed and estimated values.
Broadcast2(p) ==
  /\ loc[p] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

\* A process receives a phase-2 message and records the sender's value.
Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m.type = "phase2"
  /\ m.sender \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed, sent>>

\* Decide once enough phase-2 messages agree on the same estimated value.
Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({q \in recv[p] : [type |-> "phase2", val |-> prop[q], sender |-> q, est |-> estimate[q]].est = v})
            >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* If no estimated value reaches the threshold, fall back to choosing.
Choose(p) ==
  /\ loc[p] = "wait2"
  /\ recv[p] = 1..N
  /\ loc' = "choosing"
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, sent, recv>>

\* Deterministically pick any value seen in the local view.
Pick(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
       /\ \E q \in 1..N : view[p][q] = v
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* A process may crash silently, bounded by the fault tolerance.
Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, sent, recv>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Pick(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : Receive1(p, m) \/ Receive2(p, m)

Spec == Init /\ [][Next]_<<loc, view, prop, estimate, decided, crashed, sent, recv>>

\* Safety: a decision is always a value that some process actually proposed.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]

\* Safety: no two processes ever decide different values.
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Liveness: every process eventually crashes or finishes.
Termination == \A p \in 1..N : <>(loc[p] \in {"crashed", "done"})

\* Conditional termination: if enough processes propose the global maximum,
\* the protocol is guaranteed to terminate.
ConditionalTermination ==
  /\ \E S \in SUBSET 1..N : Cardinality(S) >= F + 1 /\ \A p \in S : prop[p] = CHOOSE m \in Values : \A q \in 1..N : prop[q] <= m
  /\ Termination

====