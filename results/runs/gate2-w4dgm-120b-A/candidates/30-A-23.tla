---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, propose, estimate, decision, crashed, sent, recv

vars == <<loc, view, propose, estimate, decision, crashed, sent, recv>>

Locations == {"bphase1", "wphase1", "prepare", "bphase2", "wphase2", "done", "crashed", "choosing"}

MaxV(S) == CHOOSE m \in S : \A x \in S : x <= m

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: 1..N]
  /\ recv \in [1..N -> SUBSET 1..N]

Init ==
  /\ loc = [p \in 1..N |-> "bphase1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "bphase1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wphase1"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

ReceivePhase1(p, m) ==
  /\ loc[p] = "wphase1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.sender \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, sent>>

ComputeEstimate(p) ==
  /\ loc[p] = "wphase1"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate[p] = Bottom
  /\ estimate' = [estimate EXCEPT ![p] = MaxV({ view[p][q] : q \in recv[p] })]
  /\ loc' = [loc EXCEPT ![p] = "bphase2"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "bphase2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> propose[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wphase2"]
  /\ UNCHANGED <<view, propose, estimate, decision, crashed, recv>>

ReceivePhase2(p, m) ==
  /\ loc[p] = "wphase2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m.sender \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, propose, estimate, decision, crashed, sent>>

Decide(p) ==
  /\ loc[p] = "wphase2"
  /\ Cardinality({q \in recv[p] : estimate[q] = estimate[p]}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = estimate[p]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Choose(p) ==
  /\ loc[p] = "wphase2"
  /\ recv[p] = 1..N
  /\ Cardinality({q \in recv[p] : estimate[q] = estimate[p]}) < N - T
  /\ decision' = [decision EXCEPT ![p] = MaxV({ view[p][q] : q \in 1..N })]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Crash ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<loc, view, propose, estimate, decision, sent, recv>>

Next ==
  \/ \E p \in 1..N: BroadcastPhase1(p) \/ ComputeEstimate(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p)
  \/ \E p \in 1..N, m \in sent: ReceivePhase1(p, m) \/ ReceivePhase2(p, m)
  \/ Crash

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N: BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1..N, m \in sent: ReceivePhase1(p, m))
  /\ WF_vars(\E p \in 1..N: ComputeEstimate(p))
  /\ WF_vars(\E p \in 1..N: BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1..N, m \in sent: ReceivePhase2(p, m))
  /\ WF_vars(\E p \in 1..N: Decide(p))
  /\ WF_vars(\E p \in 1..N: Choose(p))

Validity ==
  \A p \in 1..N: decision[p] # Bottom => \E q \in 1..N: decision[p] = propose[q]

Agreement ==
  \A p, q \in 1..N: (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  \A p \in 1..N: (loc[p] = "crashed") ~> (loc[p] \in {"done", "choosing"})

C1 ==
  \E p \in 1..N: propose[p] = MaxV({ propose[q] : q \in 1..N })

ConditionalTermination ==
  (C1) ~> (\A p \in 1..N: loc[p] \in {"done", "choosing", "crashed"})

====