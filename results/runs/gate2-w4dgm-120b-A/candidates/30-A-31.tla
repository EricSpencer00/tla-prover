---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Location: control, and msg types: p1/p2 are the two phases of the protocol.
Locations == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}
Phases == {"p1", "p2"}
Senders == 1..N
Msgs == [type : Phases, value : Values \cup {Bottom}, emitter : Senders, estimate : Values \cup {Bottom}]

VARIABLES location, view, proposed, estimate, decided, crashed, msgs, recv

TypeOK ==
  /\ location \in [Senders -> Locations]
  /\ view \in [Senders -> [Senders -> Values \cup {Bottom}]]
  /\ proposed \in [Senders -> Values]
  /\ estimate \in [Senders -> Values \cup {Bottom}]
  /\ decided \in [Senders -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq Msgs
  /\ recv \in [Senders -> SUBSET Senders]

Init ==
  /\ location = [p \in Senders |-> "broadcast1"]
  /\ view = [p \in Senders |-> [q \in Senders |-> Bottom]]
  /\ proposed \in [Senders -> Values]
  /\ estimate = [p \in Senders |-> Bottom]
  /\ decided = [p \in Senders |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recv = [p \in Senders |-> {}]

\* Phase 1: broadcast the proposal, then gather enough phase-1 messages to
\* estimate everyone's contribution via the maximum seen so far.
Broadcast1(p) ==
  /\ location[p] = "broadcast1"
  /\ msgs' = msgs \cup {[type |-> "p1", value |-> proposed[p], emitter |-> p, estimate |-> Bottom]}
  /\ location' = [location EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recv>>

Receive1(p, m) ==
  /\ location[p] = "wait1"
  /\ m.type = "p1"
  /\ m.emitter \in Senders
  /\ view[p][m.emitter] = Bottom
  /\ view' = [view EXCEPT ![p][m.emitter] = m.value]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.emitter}]
  /\ UNCHANGED <<location, proposed, estimate, decided, crashed, msgs>>

Prepare(p) ==
  /\ location[p] = "wait1"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE m \in view[p] : \A q \in Senders : view[p][q] = Bottom \/ m >= view[p][q]]
  /\ location' = "prepare"
  /\ UNCHANGED <<view, proposed, decided, crashed, msgs, recv>>

Broadcast2(p) ==
  /\ location[p] = "prepare"
  /\ msgs' = msgs \cup {[type |-> "p2", value |-> proposed[p], emitter |-> p, estimate |-> estimate[p]]}
  /\ location' = [location EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, recv>>

Receive2(p, m) ==
  /\ location[p] = "wait2"
  /\ m.type = "p2"
  /\ view[p][m.emitter] = Bottom
  /\ view' = [view EXCEPT ![p][m.emitter] = m.estimate]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.emitter}]
  /\ UNCHANGED <<location, proposed, estimate, decided, crashed, msgs>>

\* Decision: the majority estimate wins; otherwise the process must resolve.
Decide(p) ==
  /\ location[p] = "wait2"
  /\ Cardinality({x \in recv[p] : view[p][x] = estimate[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ location' = [location EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, msgs, recv>>

Choose(p) ==
  /\ location[p] = "wait2"
  /\ Cardinality({x \in recv[p] : view[p][x] = estimate[p]}) < N - T
  /\ Cardinality(recv[p]) = N
  /\ \E v \in {view[p][q] : q \in Senders} :
       /\ decided' = [decided EXCEPT ![p] = v]
       /\ location' = [location EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, msgs, recv>>

Crash(p) ==
  /\ crashed < F
  /\ location[p] \notin {"done", "crashed"}
  /\ crashed' = crashed + 1
  /\ location' = [location EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, proposed, estimate, decided, msgs, recv>>

Next ==
  \/ \E p \in Senders : Broadcast1(p) \/ Prepare(p) \/ Broadcast2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in Senders, m \in msgs : Receive1(p, m) \/ Receive2(p, m)

Spec ==
  /\ Init
  /\ [][Next]_<<location, view, proposed, estimate, decided, crashed, msgs, recv>>
  /\ WF_vars(\E p \in Senders, m \in msgs : Receive1(p, m))
  /\ WF_vars(\E p \in Senders, m \in msgs : Receive2(p, m))
  /\ WF_vars(\E p \in Senders : Decide(p))
  /\ WF_vars(\E p \in Senders : Choose(p))

\* Anything ever decided must have been proposed by some participant.
Validity == \A p \in Senders : decided[p] # Bottom => \E q \in Senders : proposed[q] = decided[p]

Agreement == \A p, q \in Senders : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Saturating the "maximum-proposed" condition guarantees termination.
C1 == Cardinality({p \in Senders : proposed[p] = CHOOSE x \in Values : \A y \in Values : x >= y}) >= F + 1
ConditionalTermination == C1 ~> (\A p \in Senders : location[p] \in {"done", "crashed"})

====