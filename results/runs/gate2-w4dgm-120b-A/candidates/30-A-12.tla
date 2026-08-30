---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

Phases == {"ph1b", "ph1w", "prep", "ph2b", "ph2w", "done", "crashed", "choose"}

VARIABLES pc, view, prop, estimate, decided, crashed, msgs, rcvd

vars == <<pc, view, prop, estimate, decided, crashed, msgs, rcvd>>

Msgs == [type : {"ph1", "ph2"}, val : Values \cup {Bottom}, est : Values \cup {Bottom}, from : 1 .. N]
\* The `est` field is a no-op for phase-1 messages; it is always present in the record for simplicity.

TypeOK ==
  /\ pc \in [1 .. N -> Phases]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ estimate \in [1 .. N -> Values \cup {Bottom}]
  /\ decided \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ msgs \subseteq Msgs
  /\ rcvd \in [1 .. N -> SUBSET 1 .. N]

Init ==
  /\ pc = [p \in 1 .. N |-> "ph1b"]
  /\ view = [p \in 1 .. N |-> [q \in 1 .. N |-> Bottom]]
  /\ prop \in [1 .. N -> Values]
  /\ estimate = [p \in 1 .. N |-> Bottom]
  /\ decided = [p \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ rcvd = [p \in 1 .. N |-> {}]

\* Phase 1, step 1: broadcast the proposed value.
BroadcastPh1(p) ==
  /\ pc[p] = "ph1b"
  /\ msgs' = msgs \cup {[type |-> "ph1", val |-> prop[p], est |-> Bottom, from |-> p]}
  /\ pc' = [pc EXCEPT ![p] = "ph1w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, rcvd>>

\* Phase 1, step 2: incorporate a phase-1 message into the local view.
RecvPh1(p) ==
  /\ pc[p] = "ph1w"
  /\ \E m \in msgs :
       /\ m.type = "ph1"
       /\ m.from \notin rcvd[p]
       /\ view' = [view EXCEPT ![p][m.from] = m.val]
       /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.from}]
  /\ UNCHANGED <<pc, prop, estimate, decided, crashed, msgs>>

\* Phase 1, step 3: enough messages gathered to compute the estimate.
Prepare(p) ==
  /\ pc[p] = "ph1w"
  /\ Cardinality(rcvd[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values : \A q \in 1 .. N : view[p][q] # Bottom => view[p][q] <= v]
  /\ pc' = "prep"
  /\ UNCHANGED <<view, prop, decided, crashed, msgs, rcvd>>

\* Phase 2, step 1: broadcast both the proposal and the estimate.
BroadcastPh2(p) ==
  /\ pc[p] = "prep"
  /\ msgs' = msgs \cup {[type |-> "ph2", val |-> prop[p], est |-> estimate[p], from |-> p]}
  /\ pc' = "ph2w"
  /\ rcvd' = [rcvd EXCEPT ![p] = {}]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed>>

\* Phase 2, step 2: incorporate a phase-2 message into the local view.
RecvPh2(p) ==
  /\ pc[p] = "ph2w"
  /\ \E m \in msgs :
       /\ m.type = "ph2"
       /\ m.from \notin rcvd[p]
       /\ view' = [view EXCEPT ![p][m.from] = m.est]
       /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.from}]
  /\ UNCHANGED <<pc, prop, estimate, decided, crashed, msgs>>

\* Phase 2, step 3a: a sufficient cluster agrees on an estimate; decide it.
DecideByQuorum(p) ==
  /\ pc[p] = "ph2w"
  /\ \E v \in Values :
       /\ {q \in 1 .. N : view[p][q] = v} \subseteq rcvd[p]
       /\ Cardinality({q \in 1 .. N : view[p][q] = v}) >= N - T
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ pc' = "done"
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcvd>>

\* Phase 2, step 3b: no estimate reached the threshold; fall back to choosing.
DecideByChoosing(p) ==
  /\ pc[p] = "ph2w"
  /\ rcvd[p] = 1 .. N
  /\ \A v \in Values : {q \in 1 .. N : view[p][q] = v} \subseteq rcvd[p] => Cardinality({q \in 1 .. N : view[p][q] = v}) < N - T
  /\ pc' = "choose"
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, msgs, rcvd>>

Choosing(p) ==
  /\ pc[p] = "choose"
  /\ \E v \in Values : view[p][p] = v /\ decided' = [decided EXCEPT ![p] = v]
  /\ pc' = "done"
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, rcvd>>

Crash ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<pc, view, prop, estimate, decided, msgs, rcvd>>

Next ==
  \/ \E p \in 1 .. N : BroadcastPh1(p) \/ RecvPh1(p) \/ Prepare(p) \/ BroadcastPh2(p) \/ RecvPh2(p) \/ DecideByQuorum(p) \/ DecideByChoosing(p) \/ Choosing(p)
  \/ Crash

Spec == Init /\ [][Next]_vars
  /\ SF_vars(\E p \in 1 .. N : BroadcastPh1(p))
  /\ SF_vars(\E p \in 1 .. N : RecvPh1(p))
  /\ SF_vars(\E p \in 1 .. N : Prepare(p))
  /\ SF_vars(\E p \in 1 .. N : BroadcastPh2(p))
  /\ SF_vars(\E p \in 1 .. N : RecvPh2(p))
  /\ SF_vars(\E p \in 1 .. N : DecideByQuorum(p))
  /\ SF_vars(\E p \in 1 .. N : DecideByChoosing(p))
  /\ WF_vars(\E p \in 1 .. N : Choosing(p))
  /\ WF_vars(Crash)

\* Every decision was proposed by someone.
Validity ==
  \A p \in 1 .. N : decided[p] # Bottom => \E q \in 1 .. N : prop[q] = decided[p]

\* Two processes never decide differently.
Agreement ==
  \A p, q \in 1 .. N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Every live process eventually reaches a decision.
Termination == \A p \in 1 .. N : (pc[p] = "crashed") ~> (decided[p] # Bottom)

\* The safe-termination condition C1: a large enough cluster proposes the maximum.
C1 ==
  LET maxVal == CHOOSE v \in Values : \A w \in Values : w <= v
  IN Cardinality({p \in 1 .. N : prop[p] = maxVal}) >= F + 1

ConditionalTermination == C1 ~> (\A p \in 1 .. N : decided[p] # Bottom)

====