---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, decision, crashed, sent, inbox

vars == <<loc, view, prop, est, decision, crashed, sent, inbox>>

\* loc: control phase per process (broadcasting, waiting, preparing, done,
\* crashed, choosing). view: per-process observation of every other's
\* value/message. prop: each process's proposed value. est: the maximum
\* value a process has observed after phase 1. decision: the chosen output,
\* always bottom until decided. inbox/sent: the message channel (unordered).
TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "p", "b2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, sender: 1..N]
  /\ inbox \in [1..N -> SUBSET [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, sender: 1..N]]

\* A process observes a value only from a message sent by that sender.
Observe(p, m) == IF m.sender = p THEN m.val ELSE view[p][m.sender]

Init ==
  /\ loc = [p \in 1..N |-> "b1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ inbox = [p \in 1..N |-> {}]

\* Phase 1: the proposed value is put on the wire (crash-stop semantics).
BroadcastPhase1(p) ==
  /\ loc[p] = "b1"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, inbox>>

RecvPhase1(p, m) ==
  /\ loc[p] \in {"w1", "p"}
  /\ m \in sent
  /\ m.type = "ph1"
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = Observe(p, m)]
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* After receiving N-T phase-1 messages, the estimate is the maximum seen.
Estimate(p) ==
  /\ loc[p] = "w1"
  /\ Cardinality({m \in inbox[p] : m.type = "ph1"}) >= N - T
  /\ est' = [est EXCEPT ![p] = CHOOSE x \in Values : \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= x]
  /\ loc' = [loc EXCEPT ![p] = "p"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, inbox>>

\* Phase 2: each process puts both its proposal and its estimate on the wire.
BroadcastPhase2(p) ==
  /\ loc[p] = "p"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, inbox>>

\* After receiving N-T phase-2 messages with one common estimate, decide it.
DecideFromCommon(p) ==
  /\ loc[p] = "w2"
  /\ \E val \in Values :
       /\ Cardinality({m \in inbox[p] : m.type = "ph2" /\ m.val = val}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = val]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, inbox>>

\* If the common estimate never forms, the process deterministically chooses
\* any value it has observed and decides it.
Choose(p) ==
  /\ loc[p] = "w2"
  /\ \A x \in Values : Cardinality({m \in inbox[p] : m.type = "ph2" /\ m.val = x}) < N - T
  /\ \E x \in Values : \E q \in 1..N : view[p][q] = x /\ decision' = [decision EXCEPT ![p] = x]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, inbox>>

\* Crash-stop failure: a process may fail silently while still batched for work.
Crash(p) ==
  /\ crashed < F
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, prop, est, decision, sent, inbox>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p)
  \/ \E p \in 1..N, m \in sent : RecvPhase1(p, m)
  \/ \E p \in 1..N : Estimate(p)
  \/ \E p \in 1..N : BroadcastPhase2(p)
  \/ \E p \in 1..N : DecideFromCommon(p)
  \/ \E p \in 1..N : Choose(p)
  \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(RecvPhase1(p, CHOOSE m \in sent : TRUE))
  /\ \A p \in 1..N : WF_vars(DecideFromCommon(p))
  /\ \A p \in 1..N : WF_vars(Choose(p))

\* A decision is always a value that some process actually proposed.
Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in {prop[q] : q \in 1..N}

\* No two processes ever decide different values.
Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Every process eventually stops (crashes or decides).
Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Under condition C1, termination is guaranteed.
ConditionalTermination == (Cardinality({p \in 1..N : prop[p] = CHOOSE x \in Values : \A y \in Values : y # Bottom => y <= x}) >= F + 1) ~> Termination

====