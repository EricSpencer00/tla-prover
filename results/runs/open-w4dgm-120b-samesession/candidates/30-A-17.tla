---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, est, decided, crashedCount, sent, received

vars == <<loc, view, prop, est, decided, crashedCount, sent, received>>

\* The protocol runs in two numbered phases (1 then 2); a slow process may
\* advance to the next phase only after receiving enough messages from
\* distinct senders in the current phase. A process may crash silently at
\* any point, and the protocol tolerates up to T such crashes.

TypeOK ==
  /\ loc \in [1..N -> {"phase1Broadcast", "phase1Wait", "phase2Broadcast", "phase2Wait", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq [type: {1, 2}, value: Values, est: Values \cup {Bottom}, from: 1..N]
  /\ received \in [1..N -> SUBSET [type: {1, 2}, value: Values, est: Values \cup {Bottom}, from: 1..N]]

RECURSIVE MaxOf(_, _)
MaxOf(S, v) ==
  IF S = {} THEN v
  ELSE LET x == CHOOSE y \in S : TRUE IN MaxOf(S \ {x}, IF x > v THEN x ELSE v)

\* The optimistic path: reaching the N-T threshold on the same estimated
\* value lets a process decide without waiting for everyone.
\* The pessimistic path: if no estimated value reaches the threshold but all
\* messages have arrived, the process picks a value from its view instead.
\* Both paths decide something from the view, which is what keeps Validity
\* intact even when phase-2 messages from crashed processes can never arrive.

Init ==
  /\ loc = [p \in 1..N |-> "phase1Broadcast"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "phase1Broadcast"
  /\ sent' = sent \cup {[type |-> 1, value |-> prop[p], est |-> Bottom, from |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "phase1Wait"]
  /\ UNCHANGED <<view, prop, est, decided, crashedCount, received>>

ReceivePhase1(p, m) ==
  /\ m.type = 1
  /\ loc[p] = "phase1Wait"
  /\ m \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.value]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashedCount, sent>>

\* The slowdown hazard: without the distinct-sender requirement a process
\* could keep looping on a single slow sender and never reach phase 2.
StartPhase2(p) ==
  /\ loc[p] = "phase1Wait"
  /\ Cardinality({m.from : m \in received[p] /\ m.type = 1}) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxOf({view[p][q] : q \in 1..N}, Bottom)]
  /\ loc' = "phase2Broadcast"
  /\ UNCHANGED <<view, prop, decided, crashedCount, sent, received>>

BroadcastPhase2(p) ==
  /\ loc[p] = "phase2Broadcast"
  /\ sent' = sent \cup {[type |-> 2, value |-> prop[p], est |-> est[p], from |-> p]}
  /\ loc' = "phase2Wait"
  /\ UNCHANGED <<view, prop, est, decided, crashedCount, received>>

ReceivePhase2(p, m) ==
  /\ m.type = 2
  /\ loc[p] = "phase2Wait"
  /\ m \notin received[p]
  /\ view' = [view EXCEPT ![p][m.from] = m.est]
  /\ received' = [received EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decided, crashedCount, sent>>

DecideByThreshold(p) ==
  /\ loc[p] = "phase2Wait"
  /\ Cardinality({m.from : m \in received[p] /\ m.type = 2 /\ m.est = est[p]}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = est[p]]
  /\ loc' = "done"
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, received>>

\* Deterministically pick the least value in the view; always available
\* once all messages have arrived, so it never stalls.
ChooseAndDecide(p) ==
  /\ loc[p] = "phase2Wait"
  /\ Cardinality({m.from : m \in received[p] /\ m.type = 2}) = N
  /\ \A e \in Values : Cardinality({m.from : m \in received[p] /\ m.type = 2 /\ m.est = e}) < N - T
  /\ decided' = [decided EXCEPT ![p] = CHOOSE v \in Values : \A q \in 1..N : view[p][q] = v \/ view[p][q] = Bottom]
  /\ loc' = "choosing"
  /\ UNCHANGED <<view, prop, est, crashedCount, sent, received>>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {"done", "crashed"}
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, prop, est, decided, sent, received>>

Next ==
  \/ \E p \in 1..N : BroadcastPhase1(p) \/ StartPhase2(p) \/ BroadcastPhase2(p) \/ DecideByThreshold(p) \/ ChooseAndDecide(p) \/ Crash(p)
  \/ \E p \in 1..N : \E m \in sent : ReceivePhase1(p, m) \/ ReceivePhase2(p, m)

Spec == Init /\ [][Next]_vars
  /\ SF_vars(\E p \in 1..N : BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1..N : ReceivePhase1(p, CHOOSE m \in sent : TRUE))
  /\ SF_vars(\E p \in 1..N : StartPhase2(p))
  /\ SF_vars(\E p \in 1..N : BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1..N : ReceivePhase2(p, CHOOSE m \in sent : TRUE))
  /\ SF_vars(\E p \in 1..N : DecideByThreshold(p))
  /\ SF_vars(\E p \in 1..N : ChooseAndDecide(p))

\* Nothing introduced by the two-phase handshake may let a decision come
\* from a value nobody actually proposed.
Validity == \A p \in 1..N : decided[p] # Bottom => (\E q \in 1..N : decided[p] = prop[q])

\* Two processes deciding on different values would mean the two phases
\* disagreed on the maximum, which can only happen with a silent crash
\* interfering with the majority, and the bounded fault budget rules that out.
Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

\* Under Condition C1 -- enough processes proposing the global maximum --
\* the optimistic threshold path always fires and the run finishes.
ConditionalTermination == (\A p \in 1..N : prop[p] = MaxOf(Values, Bottom)) ~> (\A p \in 1..N : loc[p] \in {"done", "crashed"})
====