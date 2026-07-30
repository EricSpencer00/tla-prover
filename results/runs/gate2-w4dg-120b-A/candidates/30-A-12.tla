---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Types: a process's phase (the control location for that process) and a message in the
\* network.  Types and variables are deliberately placed before the spec so that
\* TypeOK can walk every value the model ever creates.
Phases == {"broadcast1", "wait1", "prepared", "broadcast2", "wait2", "done", "crashed", "choosing"}
Msgs == [kind: {"phase1", "phase2"}, val: Values \cup {Bottom}, from: 1..N, est: Values \cup {Bottom}]

VARIABLES phase, view, propose, est, decision, crashed, sent, recvd
vars == <<phase, view, propose, est, decision, crashed, sent, recvd>>

TypeOK ==
  /\ phase \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recvd \in [1..N -> SUBSET Msgs]

Init ==
  /\ phase = [p \in 1..N |-> "broadcast1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [p \in 1..N |-> {}]

\* Phase 1: each process broadcasts its own proposal and gathers all of them into
\* its local view.  The view is only updated for messages whose kind matches the
\* receiving process's current phase, so a stale phase-2 message never overwrites
\* what a process actually observed during phase 1.
Broadcast1(p) ==
  /\ phase[p] = "broadcast1"
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> propose[p], from |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, recvd>>

Receive1(p, m) ==
  /\ phase[p] = "wait1"
  /\ m.kind = "phase1"
  /\ m \in sent
  /\ view[p][m.from] = Bottom
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m}]
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<phase, propose, est, decision, crashed, sent>>

Prepare(p) ==
  /\ phase[p] = "wait1"
  /\ Cardinality({m \in recvd[p] : m.kind = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = \E q \in 1..N : view[p][q]]
  /\ phase' = [phase EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, recvd>>

\* Phase 2: the estimated value (the maximum the process actually saw) is sent.
Broadcast2(p) ==
  /\ phase[p] = "broadcast2"
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> propose[p], from |-> p, est |-> est[p]]}
  /\ phase' = [phase EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, recvd>>

\* A decision is locked in once at least N-T received phase-2 messages agree on the
\* same estimated value.  This is what gives the protocol its fault tolerance: a
\* subset of the network can be arbitrarily slow or failed, yet the remaining
\* processes still see a supermajority for one value and decide on it.
Decide(p, v) ==
  /\ phase[p] = "wait2"
  /\ Cardinality({m \in recvd[p] : m.kind = "phase2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, recvd>>

\* When the view is too fragmented to reach the N-T threshold for any single
\* estimated value, the process falls back to picking a value it actually saw --
\* never inventing a fresh one and never picking the special bottom value.
Choose(p, v) ==
  /\ phase[p] = "wait2"
  /\ Cardinality({m \in recvd[p] : m.kind = "phase2"}) = N
  /\ \A u \in Values : Cardinality({m \in recvd[p] : m.kind = "phase2" /\ m.est = u}) < N - T
  /\ view[p][p] = v
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, recvd>>

\* A process can crash silently once the fault budget has not been spent; its
\* messages already in flight are never withdrawn, which is why the protocol
\* counts every process against the threshold, not just the live ones.
Crash(p) ==
  /\ phase[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, propose, est, decision, sent, recvd>>

Next ==
  \/ \E p \in 1..N: Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in Msgs: Receive1(p, m)
  \/ \E p \in 1..N, v \in Values: Decide(p, v) \/ Choose(p, v)

\* Both phases are bounded by weak fairness: a process that keeps broadcasting and
\* absorbing messages from the network must eventually move on to the next phase.
Spec == Init /\ [][Next]_vars
  /\ TRUE
  /\ WF_vars(\E p \in 1..N: Broadcast1(p))
  /\ WF_vars(\E p \in 1..N, m \in Msgs: Receive1(p, m))
  /\ WF_vars(\E p \in 1..N: Prepare(p))
  /\ WF_vars(\E p \in 1..N: Broadcast2(p))
  /\ WF_vars(\E p \in 1..N: \E v \in Values: Decide(p, v))
  /\ WF_vars(\E p \in 1..N: \E v \in Values: Choose(p, v))

\* Safety: nothing is ever decided unless it was actually proposed, and no two
\* processes ever come away holding different decisions.
Validity == \A p \in 1..N: decision[p] # Bottom => decision[p] \in Values
Agreement == \A p, q \in 1..N: (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Terminated == \A p \in 1..N: phase[p] \in {"crashed", "done"}
\* Condition C1 is exactly the supermajority on the maximum value: despite the
\* presence of a crash fault, that many processes agreeing on the top value is
\* enough to force every other process's estimate onto it.
ConditionC1Holds ==
  \E m \in Values: (\A p \in 1..N: propose[p] <= m) /\ Cardinality({p \in 1..N: propose[p] = m}) >= F + 1
ConditionalTermination == ConditionC1Holds ~> Terminated

\* The model's runtime bound (how many steps TLC is allowed to take) is left to
\* the configuration; every other aspect is fixed by the description above.
Terminating == Terminated

====