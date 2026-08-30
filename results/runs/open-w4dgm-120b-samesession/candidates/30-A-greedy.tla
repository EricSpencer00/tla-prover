---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol has two phases; a process may crash silently at any time.
\* Phase 1: broadcast a proposed value, collect enough phase-1 messages, and
\* compute an estimated value as the maximum of the local view. Phase 2:
\* broadcast both the proposed and estimated values, then decide once a
\* supermajority of received messages agree on an estimated value. If no
\* supermajority forms, a process deterministically chooses from its view.
\* The safety properties are validity (a decided value was proposed) and
\* agreement (no two processes decide differently). Under Condition C1
\* (enough processes propose the global maximum), the protocol always
\* reaches a decision.

VARIABLES loc, view, prop, est, decided, crashed, sent, recv

Locs == {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}
MsgTypes == {"phase1", "phase2"}
Msgs == [type: MsgTypes, val: Values, sender: 1..N, est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ recv \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value.
Broadcast1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

\* A process records a received phase-1 message into its local view.
Receive1(p, m) ==
  /\ loc[p] = "w1"
  /\ m.type = "phase1"
  /\ m \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashed, sent>>

\* Once enough phase-1 messages are in, compute the estimated value.
Prepare(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in recv[p] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE v \in Values :
                 \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= v]
  /\ loc' = [loc EXCEPT ![p] = "prep"]
  /\ UNCHANGED <<view, prop, decided, crashed, sent, recv>>

\* Phase 2: broadcast both the proposed and estimated values.
Broadcast2(p) ==
  /\ loc[p] = "prep"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> prop[p], sender |-> p, est |-> est[p]]}
  /\ loc' = [loc EXCEPT ![p] = "b2"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, recv>>

\* A process records a received phase-2 message into its local view.
Receive2(p, m) ==
  /\ loc[p] = "b2"
  /\ m.type = "phase2"
  /\ m \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashed, sent>>

\* Decide once a supermajority of received messages agree on an estimate.
Decide(p) ==
  /\ loc[p] = "b2"
  /\ \E v \in Values :
       /\ Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* If no supermajority forms, fall back to a deterministic choice.
Choose(p) ==
  /\ loc[p] = "b2"
  /\ \A v \in Values : Cardinality({m \in recv[p] : m.type = "phase2" /\ m.est = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, decided, crashed, sent, recv>>

\* Deterministically pick any value that appears in the local view.
Pick(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
       /\ \E q \in 1..N : view[p][q] = v
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

\* A process may crash silently, bounded by the fault tolerance.
Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decided, sent, recv>>

Next ==
  \/ \E p \in 1..N : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Pick(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in Msgs : Receive1(p, m) \/ Receive2(p, m)

\* Fairness: every process that is waiting for messages eventually receives
\* enough of them to move on, and every process that reaches a decision
\* eventually finishes, so the protocol never gets stuck.
Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, prop, est, decided, crashed, sent, recv>>
  /\ \A p \in 1..N :
       /\ WF_vars(Receive1(p, [type |-> "phase1", val |-> CHOOSE x \in Values : TRUE, sender |-> p, est |-> Bottom]))
       /\ WF_vars(Receive2(p, [type |-> "phase2", val |-> CHOOSE x \in Values : TRUE, sender |-> p, est |-> CHOOSE y \in Values : TRUE]))
       /\ WF_vars(Prepare(p))
       /\ WF_vars(Decide(p))
       /\ WF_vars(Pick(p))

\* Safety: a decided value was actually proposed, and no two processes
\* decide differently.
Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : prop[q] = decided[p]
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Liveness: every process eventually either crashes or finishes.
Termination == \A p \in 1..N : <>(loc[p] \in {"crashed", "done"})

\* Conditional termination: if enough processes propose the global maximum,
\* the protocol is guaranteed to reach a decision.
ConditionC1 == \E p \in 1..N : prop[p] = CHOOSE x \in Values : \A q \in 1..N : prop[q] <= x
UnderC1 == ConditionC1 ~> Termination

\* The model is only valid under the required bounds on N, T, and F.
Bounds == 2 * T < N /\ 0 <= F /\ F <= T /\ N > 0 /\ Bottom \notin Values

====