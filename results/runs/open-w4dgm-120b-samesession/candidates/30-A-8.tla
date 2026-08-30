---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES phase, view, propose, estimate, decision, crashed, sent, recv
vars == <<phase, view, propose, estimate, decision, crashed, sent, recv>>

\* Two-phase consensus; Phase 2 messages also carry the Phase 1 estimate.
TypeOK ==
  /\ phase \in [1..N -> {"bcast1", "wait1", "prep", "bcast2", "wait2", "done",
                         "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values \cup {Bottom},
                     src: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET [type: {"p1", "p2"}, val: Values \cup {Bottom},
                               src: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ phase = [i \in 1..N |-> "bcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 1..N |-> {}]

\* Phase 1: broadcast your own proposal to every process.
BcastPhase1(i) ==
  /\ phase[i] = "bcast1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> propose[i], src |-> i,
                         est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

\* Messages accumulate in an unordered buffer; delivery is nondeterministic.
Recv(i, m) ==
  /\ m \notin recv[i]
  /\ m.type = "p1"
  /\ phase[i] = "wait1"
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ UNCHANGED <<phase, propose, estimate, decision, crashed, sent>>

\* Phase 1 complete: the local view is full enough to compute the max.
Prepare(i) ==
  /\ phase[i] = "wait1"
  /\ Cardinality({m \in recv[i] : m.type = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in Values :
                     \A j \in 1..N : view[i][j] = Bottom \/ view[i][j] <= x]
  /\ phase' = [phase EXCEPT ![i] = "bcast2"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recv>>

\* Phase 2: broadcast both your proposal and your Phase-1 estimate.
BcastPhase2(i) ==
  /\ phase[i] = "bcast2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> propose[i], src |-> i,
                         est |-> estimate[i]]}
  /\ phase' = [phase EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

Recv2(i, m) ==
  /\ m \notin recv[i]
  /\ m.type = "p2"
  /\ phase[i] = "wait2"
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ estimate' = [estimate EXCEPT ![i] = IF m.est = Bottom
                                             THEN estimate[i] ELSE m.est]
  /\ UNCHANGED <<phase, propose, decision, crashed, sent>>

\* Phase 2 complete: the estimate that reached the N-T threshold wins.
DecideByEstimate(i) ==
  /\ phase[i] = "wait2"
  /\ (\E e \in Values :
        /\ Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = e}) >= N - T
        /\ decision' = [decision EXCEPT ![i] = e])
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

\* Phase 2 stalls because no single estimate reached the threshold, so pick
\* any locally visible value instead of deadlocking forever.
Choose(i) ==
  /\ phase[i] = "wait2"
  /\ Cardinality({m \in recv[i] : m.type = "p2"}) = N
  /\ \A e \in Values :
       Cardinality({m \in recv[i] : m.type = "p2" /\ m.est = e}) < N - T
  /\ phase' = [phase EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, sent, recv>>

PickChosen(i) ==
  /\ phase[i] = "choosing"
  /\ \E v \in Values :
       /\ (\E j \in 1..N : view[i][j] = v)
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Crash(i) ==
  /\ phase[i] # "crashed"
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decision, sent, recv>>

Next ==
  \/ \E i \in 1..N :
       \/ BcastPhase1(i) \/ Prepare(i) \/ BcastPhase2(i) \/ DecideByEstimate(i)
       \/ Choose(i) \/ PickChosen(i) \/ Crash(i)
       \/ \E m \in sent : Recv(i, m) \/ Recv2(i, m)

Spec == Init /\ [][Next]_vars
        /\ \A i \in 1..N :
             /\ WF_vars(\E m \in sent : Recv(i, m))
             /\ WF_vars(\E m \in sent : Recv2(i, m))
             /\ SF_vars(Prepare(i)) /\ SF_vars(DecideByEstimate(i))
             /\ SF_vars(Choose(i)) /\ SF_vars(PickChosen(i))

\* A decided value was actually proposed by some process.
Validity ==
  \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : propose[j] = decision[i]

\* No two processes ever decide different values.
Agreement ==
  \A i, j \in 1..N :
    (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Conditional termination: C1 (enough max-proposers) guarantees consensus.
ConditionalTermination ==
  (Cardinality({i \in 1..N : propose[i] = (CHOOSE x \in Values :
                                            \A j \in 1..N : propose[j] <= x)}))
    >= F + 1 => \<> (\A i \in 1..N : phase[i] \in {"done", "crashed"})
====