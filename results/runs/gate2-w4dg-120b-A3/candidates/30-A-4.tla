---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, rcvd

vars == <<loc, view, proposal, estimate, decision, crashed, sent, rcvd>>

MsgTypes == {"phase1", "phase2"}
Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> (Values \cup {Bottom})]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> (Values \cup {Bottom})]
  /\ decision \in [1..N -> (Values \cup {Bottom})]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: MsgTypes, val: Values, sender: 1..N, other: Values]
  /\ rcvd \in [1..N -> SUBSET [type: MsgTypes, val: Values, sender: 1..N, other: Values]]

\* Phase-1: broadcast a proposal; Phase-2: broadcast proposal plus an estimate.
\* A process may receive phase-1 or phase-2 messages whenever it is still alive.
\* The two-phase protocol decides once an estimate concentration exceeds the
\* failure tolerance, or otherwise picks a value from its own view.
\* Value-based agreement: decisions are drawn from local views, none invented.
Init ==
  /\ loc = [p \in 1..N |-> "broadcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [p \in 1..N |-> {}]

\* Phase-1 broadcast: a live process announces its own proposed value.
Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[p], sender |-> p, other |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, rcvd>>

\* Phase-2 broadcast: the estimate is sent along with the proposed value.
Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[p], sender |-> p, other |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, rcvd>>

\* Each process updates its local view from any matching message it receives.
Receive(p, m) ==
  /\ loc[p] \in {"wait1", "wait2"}
  /\ m \in sent
  /\ m.type = IF loc[p] = "wait1" THEN "phase1" ELSE "phase2"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = IF m.type = "phase1" THEN m.val ELSE m.other]
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

Plan1(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality(SUBSET {q \in 1..N : view[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = Cardinality({q \in 1..N : view[p][q] # Bottom})]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, rcvd>>

Plan2(p) ==
  /\ loc[p] = "wait2"
  /\ \E est \in Values :
       /\ Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.other = est}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = est]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, rcvd>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A est \in Values :
       Cardinality({m \in rcvd[p] : m.type = "phase2" /\ m.other = est}) < N - T
  /\ Cardinality({q \in 1..N : view[p][q] # Bottom}) = N
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, rcvd>>

DecideFromView(p) ==
  /\ loc[p] = "choosing"
  /\ decision[p] \in {view[p][q] : q \in 1..N}
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, rcvd>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, rcvd>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p) \/ Broadcast2(p) \/ Plan1(p) \/ Plan2(p) \/ Choose(p) \/ DecideFromView(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent : Receive(p, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E p \in 1..N, m \in sent : Receive(p, m))
        /\ WF_vars(\E p \in 1..N : Broadcast1(p))
        /\ WF_vars(\E p \in 1..N : Broadcast2(p))
        /\ WF_vars(\E p \in 1..N : Plan1(p))
        /\ WF_vars(\E p \in 1..N : Plan2(p))
        /\ WF_vars(\E p \in 1..N : Choose(p))
        /\ WF_vars(\E p \in 1..N : DecideFromView(p))

\* Every decision draws a value that was actually proposed by somebody.
Validity ==
  \A p \in 1..N : decision[p] # Bottom => decision[p] \in {proposal[q] : q \in 1..N}

\* No two processes may decide different values.
Agreement ==
  \A p, q \in 1..N :
    (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination ==
  <>(\A p \in 1..N : loc[p] \in {"crashed", "done"})

\* Condition C1: enough processes propose the maximum value to force termination.
ConditionC1 ==
  \A p \in 1..N : decision[p] = Bottom

====