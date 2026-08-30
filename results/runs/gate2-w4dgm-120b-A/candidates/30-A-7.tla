---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

\* Actions before the spec: Send1, Receive1, Send2, Receive2, Decide2,
\* Choose, Crash. The Crash action is unconstrained (any alive process may
\* crash), so the fairness assumptions are what keep it from being the
\* reason the protocol gets stuck.
CONSTANTS N, T, F, Values, Bottom

Processes == 1..N
Phases == {"phase1", "phase2", "done"}

\* Bump() is the local action for phase 1 waiting and phase 2 waiting
\* (respectively): it bumps the phase when the received-message condition is
\* satisfied, and the invariant is what keeps the two phases disjoint.
Bump(m) == [m EXCEPT !.phase = IF m.phase = "phase1" THEN "phase2" ELSE "done"]

VARIABLES loc, view, proposed, estimate, decided, crashed, msgs, received

vars == <<loc, view, proposed, estimate, decided, crashed, msgs, received>>

\* A message is one of the two-phase items: the phase it belongs to, the value
\* carried, and the sender. Phase 2 messages carry the sender's own estimate.
Msg == [ph: 1..2, val: Values \cup {Bottom}, from: Processes]

TypeOK ==
  /\ loc \in [Processes -> {"broadcast1", "phase1", "broadcast2", "phase2", "done", "crashed", "choosing"}]
  /\ view \in [Processes -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [Processes -> Values]
  /\ estimate \in [Processes -> Values \cup {Bottom}]
  /\ decided \in [Processes -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq Msg
  /\ received \in [Processes -> SUBSET Msg]

Init ==
  /\ loc = [p \in Processes |-> "broadcast1"]
  /\ view = [p \in Processes |-> [q \in 1..N |-> Bottom]]
  /\ proposed \in [Processes -> Values]
  /\ estimate = [p \in Processes |-> Bottom]
  /\ decided = [p \in Processes |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ received = [p \in Processes |-> {}]

\* Each process broadcasts its own proposed value and moves to waiting.
Send1(p) ==
  /\ loc[p] = "broadcast1"
  /\ msgs' = msgs \cup {[ph |-> 1, val |-> proposed[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "phase1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, received>>

\* The recipient's local view only records a message that matches the phase
\* it is currently waiting in, which is what keeps the two phases disjoint
\* and prevents an out-of-order delivery from contaminating the estimate.
Receive1(p, m) ==
  /\ loc[p] \in {"phase1", "phase2"}
  /\ m \in msgs
  /\ m \notin received[p]
  /\ m.ph = (IF loc[p] = "phase1" THEN 1 ELSE 2)
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashed, msgs>>

\* Once the view has been filled by at least N-T distinct senders the
\* process computes its own estimate as the maximum of what it has seen.
Bump1(p) ==
  /\ loc[p] = "phase1"
  /\ Cardinality({m \in received[p] : m.ph = 1}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] =
                    CHOOSE v \in Values : \A q \in 1..N :
                      (view[p][q] # Bottom) => (view[p][q] <= v)]
  /\ loc' = Bump([loc EXCEPT ![p], phase |-> "phase1"])
  /\ UNCHANGED <<view, proposed, decided, crashed, msgs, received>>

Send2(p) ==
  /\ loc[p] \in {"broadcast2", "phase2"}
  /\ msgs' = msgs \cup {[ph |-> 2, val |-> proposed[p], from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "phase2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, received>>

\* Phase 2 needs N-T messages sharing one estimated value, and those
\* messages are the same ones the process already counted in Bump1/Bump2.
Decide2(p) ==
  /\ loc[p] = "phase2"
  /\ Cardinality({m \in received[p] : m.ph = 2 /\ m.val = estimate[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = estimate[p]]
  /\ loc' = Bump([loc EXCEPT ![p], phase |-> "phase2"])
  /\ UNCHANGED <<view, proposed, estimate, crashed, msgs, received>>

\* If a process does not have an N-T block for a single estimated value it
\* falls back on a deterministic choice from whatever its view has.
Choose(p) ==
  /\ loc[p] = "phase2"
  /\ \A v \in Values : Cardinality({m \in received[p] : m.ph = 2 /\ m.val = v}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashed, msgs, received>>

DecideChoose(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values :
       /\ \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= v
       /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, msgs, received>>

\* Any alive process may silently crash (bounded by F, with 2T<N); the
\* fairness assumptions are what keep a crash from being the reason the
\* protocol never finishes.
Crash(p) ==
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, msgs, received>>

Bump2(p) == Bump1(p) \/ Decide2(p)

Next ==
  \/ \E p \in Processes :
       Send1(p) \/ Bump1(p) \/ Send2(p) \/ Bump2(p) \/ Choose(p) \/ DecideChoose(p) \/ Crash(p)
  \/ \E p \in Processes, m \in msgs : Receive1(p, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : Send1(p))
  /\ WF_vars(\E p \in Processes, m \in msgs : Receive1(p, m))
  /\ WF_vars(\E p \in Processes : Bump1(p))
  /\ WF_vars(\E p \in Processes : Send2(p))
  /\ WF_vars(\E p \in Processes : Bump2(p))
  /\ WF_vars(\E p \in Processes : Choose(p))
  /\ WF_vars(\E p \in Processes : DecideChoose(p))
  /\ WF_vars(\E p \in Processes : Crash(p))

\* Validity: a decision came from some proposal. Agreement: decisions never
\* diverge across the processes that made them.
Validity == \A p \in Processes : decided[p] # Bottom => \E q \in Processes : proposed[q] = decided[p]
Agreement == \A p, q \in Processes : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Under Condition C1 (at least F+1 max-value proposals) the two-phase
\* protocol never gets stuck; every process either crashes or decides.
C1 == {p \in Processes : proposed[p] = CHOOSE m \in Values : \A q \in Processes : proposed[q] <= m}
ConditionalTermination ==
  (Cardinality(C1) >= F + 1) ~> (\A p \in Processes : loc[p] \in {"done", "crashed"})

Termination == \A p \in Processes : loc[p] \in {"done", "crashed"}

====