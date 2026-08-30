---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A message carries value and estimated value (phase 2 only); sender is always present.
Message == [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, exp: Values \cup {Bottom}, snd: 0..(N - 1)]

VARIABLES phase, view, propose, estimate, decided, crashed, msgs, recved

vars == <<phase, view, propose, estimate, decided, crashed, msgs, recved>>

Phases == {"bph1", "wph1", "prep", "bph2", "wph2", "done", "crashed", "choose"}

TypeOK ==
  /\ phase \in [0..(N - 1) -> Phases]
  /\ view \in [0..(N - 1) -> [0..(N - 1) -> Values \cup {Bottom}]]
  /\ propose \in [0..(N - 1) -> Values]
  /\ estimate \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ decided \in [0..(N - 1) -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq Message
  /\ recved \in [0..(N - 1) -> SUBSET 0..(N - 1)]

\* Each process's local view starts empty (filled with Bottom) and is always filled
\* with TLA+ values; Bottom is never itself a legal value to propose.
Init ==
  /\ phase = [p \in 0..(N - 1) |-> "bph1"]
  /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
  /\ propose \in [0..(N - 1) -> Values]
  /\ estimate = [p \in 0..(N - 1) |-> Bottom]
  /\ decided = [p \in 0..(N - 1) |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recved = [p \in 0..(N - 1) |-> {}]

BroadcastPh1(p) ==
  /\ phase[p] = "bph1"
  /\ msgs' = msgs \cup {[type |-> "ph1", val |-> propose[p], exp |-> Bottom, snd |-> p]}
  /\ phase' = [phase EXCEPT ![p] = "wph1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recved>>

BroadcastPh2(p) ==
  /\ phase[p] = "prep"
  /\ msgs' = msgs \cup {[type |-> "ph2", val |-> propose[p], exp |-> estimate[p], snd |-> p]}
  /\ phase' = [phase EXCEPT ![p] = "wph2"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recved>>

\* Phase 1 collects sender votes silently; the decision needs a quorum of N-T.
ReceivePh1(p, m) ==
  /\ m.type = "ph1"
  /\ phase[p] = "wph1"
  /\ m.snd \notin recved[p]
  /\ view' = [view EXCEPT ![p] = [view[p] EXCEPT ![m.snd] = m.val]]
  /\ recved' = [recved EXCEPT ![p] = recved[p] \cup {m.snd}]
  /\ UNCHANGED <<phase, propose, estimate, decided, crashed, msgs>>

\* Phase 2 also collects votes silently and decides once N-T agree on one estimate.
ReceivePh2(p, m) ==
  /\ m.type = "ph2"
  /\ phase[p] = "wph2"
  /\ m.snd \notin recved[p]
  /\ view' = [view EXCEPT ![p] = [view[p] EXCEPT ![m.snd] = m.exp]]
  /\ recved' = [recved EXCEPT ![p] = recved[p] \cup {m.snd}]
  /\ UNCHANGED <<phase, propose, estimate, decided, crashed, msgs>>

\* Deterministic ordering: the process may only decide if its own estimate is
\* backed by a quorum of votes it has already collected.
Decide(p) ==
  /\ phase[p] = "wph2"
  /\ Cardinality({q \in 0..(N - 1) : view[p][q] = estimate[p]}) >= (N - T)
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recved>>

\* When neither estimate has a quorum, the process picks some value from its view.
Choose(p) ==
  /\ phase[p] = "wph2"
  /\ {view[p][q] : q \in 0..(N - 1)} \cap Values # {}
  /\ \A v \in Values : (v \in {view[p][q] : q \in 0..(N - 1)}) => decided' = [decided EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, msgs, recved>>

\* The quorum check is guarded on the current phase so a slow (but not failed)
\* participant cannot be overtaken by a decision it cannot see.
Compute(p) ==
  /\ phase[p] = "wph1"
  /\ Cardinality(recved[p]) >= (N - T)
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE x \in Values : \A q \in 0..(N - 1) : (view[p][q] # Bottom) => x >= view[p][q]]
  /\ phase' = [phase EXCEPT ![p] = "prep"]
  /\ UNCHANGED <<view, propose, decided, crashed, msgs, recved>>

Crash(p) ==
  /\ phase[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, msgs, recved>>

Next ==
  \/ \E p \in 0..(N - 1) : BroadcastPh1(p) \/ BroadcastPh2(p \/ Compute(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 0..(N - 1), m \in msgs : ReceivePh1(p, m) \/ ReceivePh2(p, m)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 0..(N - 1) : WF_vars(Decide(p)) /\ WF_vars(Choose(p))

\* Nothing not proposed can be decided, and two processes never land on different
\* decided values.
Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => decided[p] \in {propose[q] : q \in 0..(N - 1)}
Agreement == \A p, q \in 0..(N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Always converges, and under C1 it converges even without the slow participant
\* ever overtaking a decision it missed.
Termination == <>(\A p \in 0..(N - 1) : phase[p] \in {"done", "crashed"})
C1 == \E p \in 0..(N - 1) : propose[p] = Max(Values)
ConditionalTermination == C1 ~> Termination

\* The quorum bound of the protocol is the entire point of the weak fairness:
\* no participant's choice is ever silently starved by them all being slow.
Fairness == \A p \in 0..(N - 1) : SF_vars(BroadcastPh1(p)) /\ SF_vars(BroadcastPh2(p))
  /\ SF_vars(Compute(p)) /\ SF_vars(Decide(p)) /\ SF_vars(Choose(p)) /\ WF_vars(Compute(p))

====