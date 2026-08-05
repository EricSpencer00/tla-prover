---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, prop, estimate, decision, crashed, sent, recvd

vars == <<pc, view, prop, estimate, decision, crashed, sent, recvd>>

Type == "hb1" \/ "hb2"

Msgs == [kind : Type, val : Values, src : 1 .. N, est : Values \cup {Bottom}]

\* Each process tracks a full (N,N) view of observed values; Bottom marks
\* an entry that has not yet been learned (initially everything).
InitView == [r \in 1 .. N, c \in 1 .. N |-> Bottom]

Init ==
  /\ pc = [p \in 1 .. N |-> "hb1"]
  /\ view = [p \in 1 .. N |-> InitView]
  /\ prop \in [p \in 1 .. N |-> Values]
  /\ estimate = [p \in 1 .. N |-> Bottom]
  /\ decision = [p \in 1 .. N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [p \in 1 .. N |-> {}]

\* Phase 1: broadcast one's own proposed value.
SendH1(p) ==
  /\ pc[p] = "hb1"
  /\ sent' = sent \cup {[kind |-> "hb1", val |-> prop[p], src |-> p, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recvd>>

\* Phase 1 messages are only ever used to fill an empty entry in the view,
\* so the same (p,q) pair is never learned twice.
RecvH1(p, m) ==
  /\ m \in sent
  /\ m.kind = "hb1"
  /\ pc[p] = "w1"
  /\ view[p][m.src] = Bottom
  /\ view' = [view EXCEPT ![p][m.src] = m.val]
  /\ recvd' = [recvd EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<pc, prop, estimate, decision, crashed, sent>>

\* A process may crash at most F times; the condition 2T < N is the
\* protocol's resilience bound (at least T+1 correct processes left).
Crash(p) ==
  /\ pc[p] \notin {"done", "crashed"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, recvd>>

\* A process moves on only after observing the phase-1 messages of a
\* qualified majority (N-T distinct senders).
StartH2(p) ==
  /\ pc[p] = "w1"
  /\ Cardinality({m \in recvd[p] : m.kind = "hb1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE x \in Values :
                     \A r \in 1 .. N : view[p][r] # Bottom => view[p][r] <= x]
  /\ pc' = [pc EXCEPT ![p] = "hb2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recvd>>

\* Phase 2: broadcast the estimated value derived from the phase-1 view.
SendH2(p) ==
  /\ pc[p] = "hb2"
  /\ sent' = sent \cup {[kind |-> "hb2", val |-> prop[p], src |-> p, est |-> estimate[p]]}
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recvd>>

\* During phase 2, a process finishes if a qualified majority of phase-2
\* messages agree on some estimated value.
Decide(p, v) ==
  /\ pc[p] = "w2"
  /\ Cardinality({m \in recvd[p] : m.kind = "hb2" /\ m.est = v}) >= N - T
  /\ decision' = [decision EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recvd>>

\* If the majority threshold is never met, the process picks a value it
\* has learned (the view is non-empty once it reaches phase 2 at all).
Choose(p) ==
  /\ pc[p] = "w2"
  /\ Cardinality({m \in recvd[p] : m.kind = "hb2"}) > 0
  /\ Cardinality({m \in recvd[p] : m.kind = "hb2" /\ m.est = v}) < N - T
  /\ \A m \in recvd[p] : m.kind = "hb2" => m.est # Bottom
  /\ \E r \in 1 .. N : view[p][r] # Bottom
  /\ decision' = [decision EXCEPT ![p] = CHOOSE r \in 1 .. N : view[p][r] # Bottom]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recvd>>

\* Once every process is done, the network simply quiesces.
Quiesce ==
  /\ \A p \in 1 .. N : pc[p] \in {"done", "crashed"}
  /\ UNCHANGED vars

Next ==
  \/ Quiesce
  \/ \E p \in 1 .. N : SendH1(p) \/ StartH2(p) \/ SendH2(p) \/ Crash(p) \/ Choose(p)
  \/ \E p \in 1 .. N, v \in Values : Decide(p, v)
  \/ \E p \in 1 .. N, m \in sent : RecvH1(p, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1 .. N : SendH1(p))
  /\ WF_vars(\E p \in 1 .. N, m \in sent : RecvH1(p, m))
  /\ WF_vars(\E p \in 1 .. N : Crash(p))
  /\ WF_vars(\E p \in 1 .. N : StartH2(p))
  /\ WF_vars(\E p \in 1 .. N : SendH2(p))
  /\ WF_vars(\E p \in 1 .. N, v \in Values : Decide(p, v))
  /\ WF_vars(\E p \in 1 .. N : Choose(p))

TypeOK ==
  /\ pc \in [1 .. N -> {"hb1", "w1", "hb2", "w2", "done", "crashed"}]
  /\ view \in [1 .. N -> [1 .. N -> Values \cup {Bottom}]]
  /\ prop \in [1 .. N -> Values]
  /\ estimate \in [1 .. N -> Values \cup {Bottom}]
  /\ decision \in [1 .. N -> Values \cup {Bottom}]
  /\ crashed \in 0 .. T
  /\ sent \subseteq Msgs
  /\ recvd \in [1 .. N -> SUBSET Msgs]

Validity ==
  \A p \in 1 .. N : decision[p] # Bottom => \E q \in 1 .. N : prop[q] = decision[p]

Agreement ==
  \A p, q \in 1 .. N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

\* Condition C1: if enough processes propose the global maximum, the
\* protocol makes progress (instead of stalling on the choosing path).
Termination ==
  \A p \in 1 .. N : DecisionValue(p) => (\A q \in 1 .. N : DecisionValue(q) \/ pc[q] = "crashed")
DecisionValue(p) == decision[p] # Bottom

ConditionC1 ==
  \E S \in SUBSET (1 .. N) : Cardinality(S) >= F + 1
    /\ \A p \in S : prop[p] = CHOOSE x \in Values : \A y \in Values : y <= x

C1ImpliesTermination ==
  ConditionC1 => Termination

====