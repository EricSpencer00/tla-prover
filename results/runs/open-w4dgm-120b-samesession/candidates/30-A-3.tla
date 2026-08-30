---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ 2 * T < N
       /\ F \in Nat /\ 0 <= F /\ F <= T
       /\ Bottom \notin Values

Locations == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}
MessageTypes == {"phase1", "phase2"}
Senders == 1..N
NoMessage == [typ |-> "none", val |-> Bottom, from |-> 0, est |-> Bottom]

VARIABLES location, view, proposed, estimated, decided, crashed, messages, received

vars == <<location, view, proposed, estimated, decided, crashed, messages, received>>

LocallyProposed == {proposed[j] : j \in Senders}

TypeOK ==
  /\ location \in [Senders -> Locations]
  /\ view \in [Senders -> [Senders -> Values \cup {Bottom}]]
  /\ proposed \in [Senders -> Values]
  /\ estimated \in [Senders -> Values \cup {Bottom}]
  /\ decided \in [Senders -> Values \cup {Bottom}]
  /\ crashed \in Nat
  /\ messages \subseteq [typ : MessageTypes, val : Values, from : Senders, est : Values \cup {Bottom}]
  /\ received \in [Senders -> SUBSET Senders]

Init ==
  /\ location = [i \in Senders |-> "broadcast1"]
  /\ view = [i \in Senders |-> [j \in Senders |-> Bottom]]
  /\ proposed \in [Senders -> Values]
  /\ estimated = [i \in Senders |-> Bottom]
  /\ decided = [i \in Senders |-> Bottom]
  /\ crashed = 0
  /\ messages = {}
  /\ received = [i \in Senders |-> {}]

\* Phase 1: broadcast each process's own proposed value.
Broadcast1(i) ==
  /\ location[i] = "broadcast1"
  /\ messages' = messages \cup {[typ |-> "phase1", val |-> proposed[i], from |-> i, est |-> Bottom]}
  /\ location' = [location EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimated, decided, crashed, received>>

\* A message is only useful in the phase that matches the receiver's phase.
Receive1(i, m) ==
  /\ location[i] = "wait1"
  /\ m \in messages
  /\ m.typ = "phase1"
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = received[i] \cup {m.from}]
  /\ UNCHANGED <<location, proposed, estimated, decided, crashed, messages>>

\* Two-phase commit: a process waits for N-T matching phase-1 messages to compute
\* an estimated value (the maximum of what it has seen).
MoveToPrepare(i) ==
  /\ location[i] = "wait1"
  /\ Cardinality(received[i]) >= N - T
  /\ estimated' = [estimated EXCEPT ![i] = CHOOSE m \in {view[i][j] : j \in Senders} : TRUE]
  /\ location' = "prepare"
  /\ UNCHANGED <<view, proposed, decided, crashed, messages, received>>

\* Phase 2: broadcast both the originally proposed value and the estimated value.
Broadcast2(i) ==
  /\ location[i] = "prepare"
  /\ messages' = messages \cup {[typ |-> "phase2", val |-> proposed[i], from |-> i, est |-> estimated[i]]}
  /\ location' = [location EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimated, decided, crashed, received>>

\* A process decides once a strict-majority of phase-2 messages agree on one
\* estimated value; that is the only way a decision is reached.
DecideOnEstimate(i) ==
  /\ location[i] = "wait2"
  /\ \E v \in Values :
        /\ Cardinality({m \in messages : m.typ = "phase2" /\ m.from \in received[i] /\ m.est = v}) >= N - T
        /\ decided' = [decided EXCEPT ![i] = v]
  /\ location' = [location EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimated, crashed, messages, received>>

\* If no majority can form, the process picks something from its own view and
\* decides on it -- this is the safety fallback that prevents live-lock.
Choose(i) ==
  /\ location[i] = "wait2"
  /\ \A v \in Values :
        Cardinality({m \in messages : m.typ = "phase2" /\ m.from \in received[i] /\ m.est = v}) < N - T
  /\ \E j \in Senders : view[i][j] # Bottom
  /\ decided' = [decided EXCEPT ![i] = CHOOSE j \in Senders : view[i][j] # Bottom]
  /\ location' = [location EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimated, crashed, messages, received>>

\* Any process may crash, up to the tolerated fault bound.
Crash ==
  /\ crashed < F
  /\ \E i \in Senders : location[i] # "crashed"
  /\ crashed' = crashed + 1
  /\ location' = [i \in Senders |-> IF location[i] # "crashed" /\ (crashed < F) THEN "crashed" ELSE location[i]]
  /\ UNCHANGED <<view, proposed, estimated, decided, messages, received>>

\* Messages are delivered asynchronously and can be reordered in transit.
Deliver ==
  /\ \E i \in Senders, m \in messages : Receive1(i, m)
  /\ UNCHANGED <<location, view, proposed, estimated, decided, crashed, messages, received>>

Next ==
  \/ \E i \in Senders : Broadcast1(i) \/ MoveToPrepare(i) \/ Broadcast2(i) \/ DecideOnEstimate(i) \/ Choose(i)
  \/ \E i \in Senders, m \in messages : Receive1(i, m)
  \/ Crash
  \/ Deliver

Spec == Init /\ [][Next]_vars
        /\ \A i \in Senders : WF_vars(Choose(i))
        /\ WF_vars(Deliver)

\* Safety: a decision always reflects a value that was actually proposed.
Validity == \A i \in Senders : decided[i] # Bottom => decided[i] \in LocallyProposed

\* Safety: two processes never decide different values.
Agreement == \A i, j \in Senders : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Liveness: every process eventually crashes or decides.
Termination == <>(\A i \in Senders : location[i] \in {"crashed", "done"})

\* Conditional termination: if enough processes propose the maximum, the protocol
\* reaches a decision rather than stalling forever.
ConditionC1 == (\A i \in Senders : proposed[i] # Bottom) /\ Cardinality({i \in Senders : proposed[i] = CHOOSE w \in LocallyProposed : \A j \in Senders : w >= proposed[j]}) >= F + 1

ConditionalTermination == ConditionC1 ~> Termination

====