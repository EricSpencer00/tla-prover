---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase commit: phase 1 collects proposals, phase 2 collects
\* estimates; a process may crash silently at any point.  Max aggregation
\* drives termination under Condition C1 (F+1 propose the maximum).
VARIABLES loc, view, propose, estimate, decision, crashed, sent, recv

Locs == {"ph1bcast", "ph1wait", "ph2prep", "ph2bcast", "ph2wait", "done", "crashed", "choosing"}

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"ph1", "ph2"}, value: Values, sender: 1..N]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [p \in 1..N |-> "ph1bcast"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

MaxV(S) == CHOOSE m \in S :
  /\ \A x \in S : m >= x
  /\ Cardinality(S) = Cardinality(S)

BroadcastPh1(p) ==
  /\ loc[p] = "ph1bcast"
  /\ sent' = sent \cup {[type |-> "ph1", value |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "ph1wait"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

ReceivePh1(p, m) ==
  /\ loc[p] = "ph1wait"
  /\ m.type = "ph1"
  /\ p \notin recv[m.sender]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
  /\ loc[p] = "ph1wait"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxV({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "ph2prep"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recv>>

BroadcastPh2(p) ==
  /\ loc[p] = "ph2prep"
  /\ sent' = sent \cup {[type |-> "ph2", value |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "ph2wait"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

ReceivePh2(p, m) ==
  /\ loc[p] = "ph2wait"
  /\ m.type = "ph2"
  /\ p \notin recv[m.sender]
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, sent>>

DecideByMajority(p) ==
  /\ loc[p] = "ph2wait"
  /\ Cardinality({q \in 1..N : view[p][q] = estimate[p] /\ view[p][q] # Bottom}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Choose(p) ==
  /\ loc[p] = "ph2wait"
  /\ recv[p] = 1..N
  /\ loc[p] # "choosing"
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, sent, recv>>

DecideByChoice(p) ==
  /\ loc[p] = "choosing"
  /\ decision' = [decision EXCEPT ![p] = MaxV({view[p][q] : q \in 1..N})]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Crash(p) ==
  /\ loc[p] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decision, sent, recv>>

Next ==
  \/ \E p \in 1..N : BroadcastPh1(p) \/ ComputeEstimate(p) \/ BroadcastPh2(p) \/ DecideByMajority(p) \/ Choose(p) \/ DecideByChoice(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : ReceivePh1(p, m) \/ ReceivePh2(p, m)

Spec == Init /\ [][Next]_<<loc, view, propose, estimate, decision, crashed, sent, recv>>

ValidDecision == \A p \in 1..N : decision[p] # Bottom => \E q \in 1..N : propose[q] = decision[p]

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

====