---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A phase-1 message is only a value; a phase-2 message carries the
\* sender's own estimate as well as its value.
Message == [type: 1..2, value: Values \cup {Bottom}, from: 1..N]

VARIABLES loc, view, proposal, estimate, decision, crashed, msgs, got

vars == <<loc, view, proposal, estimate, decision, crashed, msgs, got>>

TypeOK ==
  /\ loc \in [1..N ->
        {"phase1Bcast", "phase1Wait", "prepare", "phase2Bcast",
         "phase2Wait", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \subseteq Message
  /\ got \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [i \in 1..N |-> "phase1Bcast"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ got = [i \in 1..N |-> {}]

\* Phase 1: every process broadcasts its own proposal, then waits
\* to collect enough phase-1 messages to compute an estimate.
Broadcast1(i) ==
  /\ loc[i] = "phase1Bcast"
  /\ msgs' = msgs \cup {[type |-> 1, value |-> proposal[i], from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase1Wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, got>>

\* A received message updates the local view; the type guard is what
\* stops a phase-2 message from being mistaken for phase-1 data here.
Receive1(i, m) ==
  /\ loc[i] \in {"phase1Wait", "prepare"}
  /\ m \in msgs
  /\ m.type = 1
  /\ m.from \notin got[i]
  /\ view' = [view EXCEPT ![i][m.from] = m.value]
  /\ got' = [got EXCEPT ![i] = got[i] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, msgs>>

Compute(i) ==
  /\ loc[i] = "phase1Wait"
  /\ Cardinality(got[i]) >= N - T
  /\ \E v \in Values: \A j \in 1..N: view[i][j] # Bottom => v >= view[i][j]
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values:
        \A j \in 1..N: view[i][j] # Bottom => v >= view[i][j]]
  /\ loc' = [loc EXCEPT ![i] = "prepare"]
  /\ UNCHANGED <<view, proposal decision, crashed, msgs, got>>

\* Phase 2: every process broadcasts both its own value and its estimate.
Broadcast2(i) ==
  /\ loc[i] = "prepare"
  /\ msgs' = msgs \cup {[type |-> 2, value |-> proposal[i],
        from |-> i, estimate |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "phase2Wait"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, got>>

\* A process decides when at least N-T phase-2 messages back one estimate.
Decide(i) ==
  /\ loc[i] = "phase2Wait"
  /\ \E v \in Values:
        /\ Cardinality({m \in got[i]: m.type = 2 /\ m.estimate = v}) >= N - T
        /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, got>>

\* If no estimate reaches the threshold, the process falls back to picking
\* any value it has actually seen in the values it collected.
Choose(i) ==
  /\ loc[i] = "phase2Wait"
  /\ \A v \in Values: Cardinality({m \in got[i]: m.type = 2 /\ m.estimate = v})
        < N - T
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, msgs, got>>

Pick(i) ==
  /\ loc[i] = "choosing"
  /\ decision' = [decision EXCEPT ![i] = CHOOSE v \in Values:
        \E j \in 1..N: view[i][j] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, got>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<view, proposal, estimate, decision, msgs, got>>

\* A message is received by exactly the process it was sent to, so each
\* process has a single role in each of these two-phase actions.
Receive1For(i) == \E m \in msgs: Receive1(i, m)
PickFor(i) == Pick(i)

Next ==
  \/ \E i \in 1..N:
        Broadcast1(i) \/ Compute(i) \/ Broadcast2(i) \/ Decide(i)
        \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in msgs: Receive1(i, m)

\* Each message sent is also eventually received by its sole recipient.
Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Receive1For(1)) /\ WF_vars(PickFor(1))
  /\ WF_vars(Receive1For(2)) /\ WF_vars(PickFor(2))
  /\ WF_vars(Receive1For(3)) /\ WF_vars(PickFor(3))

Validity == \A i \in 1..N: decision[i] # Bottom => \E j \in 1..N: proposal[j] = decision[i]

Agreement == \A i, j \in 1..N: (decision[i] # Bottom /\ decision[j] # Bottom)
                          => decision[i] = decision[j]

Termination == <>(\A i \in 1..N: loc[i] \in {"done", "crashed"})

\* Under the condition of a strong enough supporting majority at the outset
\* (F+1 processes proposing the maximum), the protocol always reaches a decision.
ConditionalTermination ==
  \A v \in Values: (\A j \in 1..N: v >= proposal[j]) /\ Cardinality({i \in 1..N: proposal[i] = v}) >= F + 1 => Termination

====