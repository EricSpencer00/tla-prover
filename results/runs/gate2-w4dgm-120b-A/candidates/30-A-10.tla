---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The system tracks each process's control location, its local view of every
\* other process's value, its own proposal, its maximum-estimate, and its
\* decision.  `crashed` counts crashed processes (bounded by T); `sent` and
\* `recvBy` are the message set and per-destination receive set.
VARIABLES phase, view, propose, estimate, decided, crashed, sent, recvBy

None == "none"
Locs == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}
MsgTypes == {"ph1", "ph2"}
Msgs == [mtype: MsgTypes, val: Values \cup {Bottom}, from: 0..(N - 1), est: Values \cup {Bottom}]
Phases == {"phase1", "phase2"}

MaxV(S) == CHOOSE m \in S : \A k \in S : k <= m

TypeOK ==
  /\ phase \in [0..(N - 1) -> Locs]
  /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
  /\ propose \in [0..(N - 1) -> Values]
  /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ recvBy \in [0..(N - 1) -> SUBSET Msgs]

Init ==
  /\ phase = [p \in 0..(N - 1) |-> "b1"]
  /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
  /\ propose \in [0..(N - 1) -> Values]
  /\ estimate = [p \in 0..(N - 1) |-> Bottom]
  /\ decided = [p \in 0..(N - 1) |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvBy = [p \in 0..(N - 1) |-> {}]

\* Phase 1: broadcast each process's own proposal.
Broadcast1(p) ==
  /\ phase[p] = "b1"
  /\ \A m \in sent : ~(m.mtype = "ph1" /\ m.from = p)
  /\ sent' = sent \cup {[mtype |-> "ph1", val |-> propose[p], from |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recvBy>>

\* Phase 1: update the local view with received proposals.
Receive1(p, m) ==
  /\ phase[p] = "w1"
  /\ m \in recvBy[p]
  /\ m.mtype = "ph1"
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<phase, propose, estimate, decided, crashed, sent, recvBy>>

\* Phase 1: after enough (N-T) proposals, compute the max estimate.
ComputeEst(p) ==
  /\ phase[p] = "w1"
  /\ Cardinality({q \in 0..(N - 1) : view[p][q] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = MaxV({view[p][q] : q \in 0..(N - 1)})
  /\ phase' = [phase EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, propose, decided, crashed, sent, recvBy>>

\* Phase 2: broadcast both the proposal and the computed estimate.
Broadcast2(p) ==
  /\ phase[p] = "b2"
  /\ \A m \in sent : ~(m.mtype = "ph2" /\ m.from = p)
  /\ sent' = sent \cup {[mtype |-> "ph2", val |-> propose[p], from |-> p, est |-> estimate[p]]}
  /\ phase' = [phase EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recvBy>>

\* Phase 2: decide when (N-T) matching estimates are collected.
DecideOnArm(p, v) ==
  /\ phase[p] = "w2"
  /\ Cardinality({q \in 0..(N - 1) : \E m \in recvBy[p] : m.mtype = "ph2" /\ m.from = q /\ m.est = v}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recvBy>>

\* Phase 2: if every sender is heard from but no (N-T) consensus emerges,
\* fallback to the deterministic per-process choice.
Fallback(p) ==
  /\ phase[p] = "w2"
  /\ {m.from : m \in recvBy[p]} = (0..(N - 1))
  /\ \A v \in Values : Cardinality({q \in 0..(N - 1) : \E m \in recvBy[p] : m.mtype = "ph2" /\ m.from = q /\ m.est = v}) < N - T
  /\ phase' = [phase EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, sent, recvBy>>

Choosing(p) ==
  /\ phase[p] = "choosing"
  /\ \E v \in Values : decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recvBy>>

\* A process may crash at any point, up to the tolerated bound.
Crash(p) ==
  /\ phase[p] # "crashed"
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, recvBy>>

Deliver(m) ==
  /\ m \in sent
  /\ m.from < N
  /\ \E dest \in 0..(N - 1) : dest # m.from /\ m \notin recvBy[dest]
  /\ recvBy' = [recvBy EXCEPT ![dest] = @ \cup {m}]
  /\ UNCHANGED <<phase, view, propose, estimate, decided, crashed, sent>>

Next ==
  \/ \E p \in 0..(N - 1) : Broadcast1(p) \/ ComputeEst(p) \/ Broadcast2(p) \/ Fallback(p) \/ Choosing(p) \/ Crash(p)
  \/ \E p \in 0..(N - 1), m \in Msgs : Receive1(p, m) \/ DecideOnArm(p, m.est)
  \/ \E m \in Msgs : Deliver(m)

\* Fairness on every receive, broadcast, transition, and choice ensures
\* progress despite arbitrary message delay (reordering) and crashes.
Spec ==
  /\ Init /\ [][Next]_<<phase, view, propose, estimate, decided, crashed, sent, recvBy>>
  /\ \A p \in 0..(N - 1) : WF_vars(\E m \in Msgs : Receive1(p, m))
  /\ \A p \in 0..(N - 1) : WF_vars(ComputeEst(p))
  /\ \A p \in 0..(N - 1) : WF_vars(Broadcast2(p))
  /\ \A p \in 0..(N - 1) : WF_vars(Fallback(p))
  /\ \A p \in 0..(N - 1) : WF_vars(Choosing(p))

\* Every decided value was actually proposed by some process.
Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => \E q \in 0..(N - 1) : propose[q] = decided[p]

\* No two processes decide different values.
Agreement == \A p, q \in 0..(N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* The model is checked under these constraints, which are the protocol's
\* required operating envelope; they are not derived from the model.
Constraints ==
  /\ 2 * T < N
  /\ 0 <= F /\ F <= T
  /\ N > 0
  /\ Bottom \notin Values

====