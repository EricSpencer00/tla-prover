---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 broadcast sends only the proposed value; phase-2 broadcast sends
\* both the proposed value and the (already computed) estimated value.
Message == [type : {"phase1", "phase2"}, value : Values, est : Values \cup {Bottom}, from : 1..N]

VARIABLES loc, view, propose, est, decision, crashed, sent, inbox
vars == <<loc, view, propose, est, decision, crashed, sent, inbox>>

Locations == {"phase1-broadcast", "phase1-wait", "prepare",
              "phase2-broadcast", "phase2-wait",
              "done", "crashed", "choosing"}

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ inbox \in [1..N -> SUBSET Message]

Init ==
  /\ loc = [i \in 1..N |-> "phase1-broadcast"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ inbox = [i \in 1..N |-> {}]

BroadcastPhase1(i) ==
  /\ loc[i] = "phase1-broadcast"
  /\ sent' = sent \cup {[type |-> "phase1", value |-> propose[i], est |-> Bottom, from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase1-wait"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, inbox>>

ReceivePhase1(i, m) ==
  /\ loc[i] = "phase1-wait"
  /\ m.type = "phase1"
  /\ m \notin inbox[i]
  /\ inbox' = [inbox EXCEPT ![i] = @ \cup {m}]
  /\ view' = [view EXCEPT ![i][m.from] = m.value]
  /\ UNCHANGED <<loc, propose, est, decision, crashed, sent>>

\* Once the quorum of N-T distinct phase-1 messages has been received, the
\* maximum of the accumulated view is the estimated value.
Prepare(i) ==
  /\ loc[i] = "phase1-wait"
  /\ Cardinality({m \in inbox[i] : m.type = "phase1"}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE x \in Values : \A y \in Values : (x >= y /\ \A z \in 1..N : view[i][z] # Bottom => y >= view[i][z]) /\ x >= propose[i]]
  /\ loc' = [loc EXCEPT ![i] = "phase2-broadcast"]
  /\ UNCHANGED <<view, propose, decision, crashed, sent, inbox>>

BroadcastPhase2(i) ==
  /\ loc[i] = "phase2-broadcast"
  /\ sent' = sent \cup {[type |-> "phase2", value |-> propose[i], est |-> est[i], from |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase2-wait"]
  /\ UNCHANGED <<view, propose, est, decision, crashed, inbox>>

ReceivePhase2(i, m) ==
  /\ loc[i] = "phase2-wait"
  /\ m.type = "phase2"
  /\ m \notin inbox[i]
  /\ inbox' = [inbox EXCEPT ![i] = @ \cup {m}]
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ UNCHANGED <<loc, propose, est, decision, crashed, sent>>

DecideByQuorum(i) ==
  /\ loc[i] = "phase2-wait"
  /\ \E v \in Values :
       /\ Cardinality({m \in inbox[i] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, inbox>>

\* If the quorum condition is never met, fall back to picking whatever the
\* current view already holds (deterministic choice, never bottom).
Choose(i) ==
  /\ loc[i] = "phase2-wait"
  /\ \A m \in inbox[i] : m.type = "phase2"
  /\ \E v \in Values :
       /\ v \in {view[i][j] : j \in 1..N}
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, inbox>>

DecideByChoosing(i) ==
  /\ loc[i] = "choosing"
  /\ decision' = [decision EXCEPT ![i] = est[i]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, est, crashed, sent, inbox>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] \notin {"done", "crashed"}
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, est, decision, sent, inbox>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i) \/ Prepare(i) \/ BroadcastPhase2(i) \/ DecideByQuorum(i) \/ Choose(i) \/ DecideByChoosing(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Message : ReceivePhase1(i, m) \/ ReceivePhase2(i, m)

Spec ==
  /\ Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in Message : ReceivePhase1(i, m))
  /\ WF_vars(\E i \in 1..N, m \in Message : ReceivePhase2(i, m))
  /\ WF_vars(\E i \in 1..N : BroadcastPhase1(i))
  /\ WF_vars(\E i \in 1..N : BroadcastPhase2(i))
  /\ WF_vars(\E i \in 1..N : Prepare(i))
  /\ WF_vars(\E i \in 1..N : DecideByQuorum(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))
  /\ WF_vars(\E i \in 1..N : DecideByChoosing(i))

Validity ==
  \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : propose[j] = decision[i]

Agreement ==
  \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination ==
  \A i \in 1..N : loc[i] = "crashed" \/ decision[i] # Bottom

ConditionC1 ==
  \E S \in SUBSET (1..N) : Cardinality(S) >= F + 1 /\ \A i \in S : propose[i] = CHOOSE v \in Values : \A w \in Values : w >= v
====