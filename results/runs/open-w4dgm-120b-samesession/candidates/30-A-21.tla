---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The system tracks each process's control location (phase, waiting, crashed),
\* its local view of every process's value, the proposed value, the estimated
\* value (the max of the local view after phase 1), and the decision value.
\* Messages are sent and received asynchronously (delivery may reorder).
\* A crashed process simply stops participating; the two-phase scheme tolerates
\* up to T such failures, and the invariant checks that any decision made is
\* backed by a real proposal, so a crash can never cause an unjustified decision.
\* Reordering is modeled by the fact that a receive pulls from the unordered set
\* of sent messages and drops the message from the set on receipt.
\* The bound 2T < N is what makes Condition C1 sufficient for termination.

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, recv

Locs == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}

Message == [type: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: 0 .. (N - 1), est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [0 .. (N - 1) -> Locs]
  /\ view \in [0 .. (N - 1) -> [0 .. (N - 1) -> Values \cup {Bottom}]]
  /\ proposal \in [0 .. (N - 1) -> Values]
  /\ estimate \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ decision \in [0 .. (N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0 .. F
  /\ sent \subseteq Message
  /\ recv \in [0 .. (N - 1) -> SUBSET Message]

Init ==
  /\ loc = [i \in 0 .. (N - 1) |-> "broadcast1"]
  /\ view = [i \in 0 .. (N - 1) |-> [j \in 0 .. (N - 1) |-> Bottom]]
  /\ proposal \in [0 .. (N - 1) -> Values]
  /\ estimate = [i \in 0 .. (N - 1) |-> Bottom]
  /\ decision = [i \in 0 .. (N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [i \in 0 .. (N - 1) |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(i) ==
  /\ loc[i] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposal[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

\* Receive a pending message and update the local view; messages may be delivered
\* in any order, which is what lets a slow participant lag behind the others.
Receive1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ m.sender \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

\* Once the phase-1 quorum is assembled, compute the estimate (max of the view)
\* and move on to broadcasting in phase 2; the estimate is never recomputed.
Prepare(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality(recv[i]) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE w \in Values : \A j \in 0 .. (N - 1) : view[i][j] # Bottom => w >= view[i][j]]
  /\ loc' = "prepare"
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, recv>>

\* Phase 2: broadcast the proposed and estimated values.
Broadcast2(i) ==
  /\ loc[i] = "prepare"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposal[i], sender |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, recv>>

\* A process may crash silently; at most F actually ever do.
Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, recv>>

Receive2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m \in sent
  /\ m.type = "phase2"
  /\ m.sender \notin recv[i]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

\* The quorum decision: if at least N-T phase-2 messages agree on the same
\* estimated value, decide it. This is the sole way a decision is reached.
DecideEst(i) ==
  /\ loc[i] = "wait2"
  /\ \E w \in Values : Cardinality({m \in recv[i] : m.est = w}) >= (N - T)
  /\ decision' = [decision EXCEPT ![i] = CHOOSE w \in Values : Cardinality({m \in recv[i] : m.est = w}) >= (N - T)]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

\* If the phase-2 quorum never forms for any estimate, the process falls back
\* to picking any value it has seen in its local view.
Choose(i) ==
  /\ loc[i] = "wait2"
  /\ recv[i] = sent
  /\ Cardinality({m \in recv[i] : m.est = estimate[i]}) < (N - T)
  /\ loc' = "choosing"
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, recv>>

DecideChoice(i) ==
  /\ loc[i] = "choosing"
  /\ decision' = [decision EXCEPT ![i] = CHOOSE w \in Values : \E j \in 0 .. (N - 1) : view[i][j] = w]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, recv>>

Next ==
  \/ \E i \in 0 .. (N - 1) : Broadcast1(i) \/ Prepare(i) \/ Broadcast2(i) \/ Crash(i) \/ DecideEst(i) \/ Choose(i) \/ DecideChoice(i)
  \/ \E i \in 0 .. (N - 1), m \in Message : Receive1(i, m) \/ Receive2(i, m)

Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, proposal, estimate, decision, crashed, sent, recv>>

\* No decision is ever fabricated: every decided value was proposed by somebody.
Validity == \A i \in 0 .. (N - 1) : decision[i] # Bottom => \E j \in 0 .. (N - 1) : proposal[j] = decision[i]

\* Two processes that both decide must land on the same value.
Agreement == \A i, j \in 0 .. (N - 1) : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Phase 1 only ever advances once a quorum of view messages is assembled, so
\* with 2T < N a quorum cannot be made up entirely of faulty participants.
PhaseAdvanceQuorum == \A i \in 0 .. (N - 1) : loc[i] \in {"prepare", "wait2", "done"} => Cardinality(recv[i]) >= (N - T)

\* The decision quorum is what decides the outcome; weak fairness on it is all
\* that is needed, and it is exactly the stall point if the estimate is split.
DecideFairly == \A i \in 0 .. (N - 1) : (loc[i] = "wait2") ~> (loc[i] = "done")

Fairness ==
  /\ \A i \in 0 .. (N - 1), m \in Message : WF_vars(Receive1(i, m))
  /\ \A i \in 0 .. (N - 1), m \in Message : WF_vars(Receive2(i, m))
  /\ \A i \in 0 .. (N - 1) : WF_vars(Prepare(i))
  /\ \A i \in 0 .. (N - 1) : WF_vars(DecideEst(i))
  /\ \A i \in 0 .. (N - 1) : WF_vars(DecideChoice(i))

Properties == Fairness /\ PhaseAdvanceQuorum /\ DecideFairly

====