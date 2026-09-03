---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The system tracks each process's control location, its local view of every
\* other process's value, its own proposed value, its estimated value (the
\* maximum it has seen), and its decision.  Messages are sent and received
\* asynchronously; a process may crash silently at any time.
\* The invariant is agreement: no two processes ever decide different values.

VARIABLES loc, view, prop, estimate, decision, crashed, sent, recv

vars == <<loc, view, prop, estimate, decision, crashed, sent, recv>>

Phases == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}
Msgs == [type: MsgTypes, val: Values, sender: 0..(N - 1), est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [0..(N - 1) -> Phases]
  /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
  /\ prop \in [0..(N - 1) -> Values]
  /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ decision \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [0..(N - 1) -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 0..(N - 1) |-> "broadcast1"]
  /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
  /\ prop \in [0..(N - 1) -> Values]
  /\ estimate = [p \in 0..(N - 1) |-> Bottom]
  /\ decision = [p \in 0..(N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 0..(N - 1) |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* A process may receive a phase-1 message and update its local view.
Receive1(p, m) ==
  /\ loc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* Once enough phase-1 messages are in, compute the maximum estimate and move
\* to phase 2.
Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({m \in recv[p] : m.type = "phase1"}) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                     \A q \in 0..(N - 1) : view[p][q] # Bottom => view[p][q] <= v]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

\* Phase 2: broadcast both the proposed value and the estimated maximum.
Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* A process may receive a phase-2 message and update its local view.
Receive2(p, m) ==
  /\ loc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* If at least N-T phase-2 messages agree on an estimated value, decide it.
Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) >= (N - T)
       /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* If all phase-2 messages are in but no value reached the N-T threshold,
\* the process deterministically picks a value from its view.
Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A q \in 0..(N - 1) : view[p][q] # Bottom
  /\ \A v \in Values :
       Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < (N - T)
  /\ decision' = [decision EXCEPT ![p] = CHOOSE q \in 0..(N - 1) : view[p][q] # Bottom]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

\* A process in the choosing state finalizes its deterministic choice.
Finalize(p) ==
  /\ loc[p] = "choosing"
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, recv>>

\* A process may crash silently, provided the fault budget is not exceeded.
Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
  \/ \E p \in 0..(N - 1) : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Finalize(p) \/ Crash(p)
  \/ \E p \in 0..(N - 1), m \in Msgs : Receive1(p, m) \/ Receive2(p, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 0..(N - 1) : WF_vars(Decide(p))
  /\ \A p \in 0..(N - 1) : WF_vars(Finalize(p))

\* Validity: a decided value was actually proposed by some process.
Validity == \A p \in 0..(N - 1) : decision[p] # Bottom => \E q \in 0..(N - 1) : prop[q] = decision[p]

\* Agreement: no two processes ever decide different values.
Agreement == \A p, q \in 0..(N - 1) : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

====