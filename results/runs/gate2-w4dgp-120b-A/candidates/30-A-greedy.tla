---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0 /\ T \in Nat /\ F \in Nat /\ T >= F /\ 2 * T < N /\ Bottom \notin Values

VARIABLES loc, view, prop, estimate, decision, crashed, sent, received

vars == <<loc, view, prop, estimate, decision, crashed, sent, received>>

\* loc: each process's control location in the two-phase protocol.
\* view: each process's local view of every other process's value (N-by-N matrix).
\* prop: each process's proposed value; estimate: the max of its view after phase 1.
\* decision: the value a process decided on; crashed: number of crashed processes.
\* sent: all messages sent; received: messages each process has received.
\* Messages carry a type (phase 1 or phase 2), a value, and a sender; phase 2
\* messages also carry an estimated value.

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "p", "b2", "w2", "done", "crashed", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values, from: 1..N, est: Values \cup {Bottom}]
  /\ received \in [1..N -> SUBSET [type: {"p1", "p2"}, val: Values, from: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* Phase 1: each process broadcasts its proposed value.
Broadcast1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> prop[i], from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* A process receives a phase-1 message and updates its local view.
Receive1(i, m) ==
  /\ loc[i] = "w1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* Once a process has heard from enough distinct senders, it computes its
\* estimate as the maximum value in its view and moves to phase 2.
Prepare(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({m.from : m \in received[i] : m.type = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE v \in Values :
                     \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= v]
  /\ loc' = [loc EXCEPT ![i] = "p"]
  /\ UNCHANGED <<view, prop, crashed, sent, received, decision>>

\* Phase 2: each process broadcasts both its proposed value and its estimate.
Broadcast2(i) ==
  /\ loc[i] = "p"
  /\ sent' = sent \cup {[type |-> "p2", val |-> prop[i], from |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, received>>

\* A process receives a phase-2 message and updates its view.
Receive2(i, m) ==
  /\ loc[i] = "w2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, estimate, decision, crashed, sent>>

\* If enough phase-2 messages agree on the same estimate, the process decides.
Decide(i) ==
  /\ loc[i] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({m \in received[i] : m.type = "p2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* If no estimate reaches the N-T threshold, the process deterministically
\* chooses a value from its view and decides it.
Choose(i) ==
  /\ loc[i] = "w2"
  /\ \A j \in 1..N : view[i][j] # Bottom
  /\ \A v \in Values :
       Cardinality({j \in 1..N : view[i][j] = v}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, received>>

DecideChosen(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, received>>

\* A process may crash, provided fewer than F have crashed so far.
Crash(i) ==
  /\ loc[i] \notin {"crashed", "done"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<view, prop, estimate, decision, sent, received>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Prepare(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ DecideChosen(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in sent : Receive1(i, m) \/ Receive2(i, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N, m \in sent : Receive1(i, m))
        /\ WF_vars(\E i \in 1..N, m \in sent : Receive2(i, m))
        /\ WF_vars(\E i \in 1..N : Prepare(i))
        /\ WF_vars(\E i \in 1..N : Decide(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))
        /\ WF_vars(\E i \in 1..N : DecideChosen(i))

\* Validity: a decided value was actually proposed by some process.
Validity == \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : prop[j] = decision[i]

\* Agreement: no two processes decide different values.
Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Termination: every process either crashes or finishes with a decision.
Termination == <>(\A i \in 1..N : loc[i] \in {"crashed", "done"})

\* Conditional termination: if enough processes propose the maximum value, the
\* protocol terminates.
ConditionC1 == \E i \in 1..N : prop[i] = CHOOSE v \in Values : \A j \in 1..N : prop[j] <= v
TerminationC1 == ConditionC1 ~> (\A i \in 1..N : loc[i] \in {"crashed", "done"})

====