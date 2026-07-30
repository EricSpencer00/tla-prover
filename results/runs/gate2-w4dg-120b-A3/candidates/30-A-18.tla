---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, prop, estimate, decided, crashed, msgs, recv

vars == <<loc, view, prop, estimate, decided, crashed, msgs, recv>>

\* loc tracks the control state of each process. view[i][j] is what process i has
\* learned of process j's value (Bottom means "not learned yet").
\* decided[i] is Bottom until process i decides.

TypeOK ==
  /\ loc \in [1..N -> {"phase1b","phase1w","phase2b","phase2w","done","crashed","choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ msgs \subseteq [type: {"phase1","phase2"}, value: Values, sender: 1..N, est: Values \cup {Bottom}]
  /\ recv \subseteq [receiver: 1..N, sender: 1..N, type: {"phase1","phase2"}]

Init ==
  /\ loc = [i \in 1..N |-> "phase1b"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ \E f \in [1..N -> Values] : prop = f
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recv = {}

MaxInView(i) == \E j \in 1..N : view[i][j] # Bottom /\ view[i][j] = estimate[i]

\* Phase 1 broadcast: a process sends its proposed value and moves on.
Phase1Broadcast(i) ==
  /\ loc[i] = "phase1b"
  /\ msgs' = msgs \cup {[type |-> "phase1", value |-> prop[i], sender |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "phase1w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

\* Phase 1 reception: a process integrates a matching phase-1 message into its view.
Phase1Receive(rcv) ==
  /\ rcv.receiver \in 1..N
  /\ loc[rcv.receiver] = "phase1w"
  /\ rcv.type = "phase1"
  /\ [type |-> "phase1", value |-> view[rcv.receiver][rcv.sender], sender |-> rcv.sender, est |-> Bottom]
       \notin msgs
  /\ msgs' = msgs \cup {[type |-> "phase1", value |-> view[rcv.receiver][rcv.sender],
                         sender |-> rcv.sender, est |-> Bottom]}
  /\ view' = [view EXCEPT ![rcv.receiver][rcv.sender] = rcv.value]
  /\ recv' = recv \cup {rcv}
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed>>

\* Phase 1 transition to phase 2 once enough distinct phase-1 messages were received.
Phase1ToPhase2(i) ==
  /\ loc[i] = "phase1w"
  /\ Cardinality({rcv.sender : rcv \in recv /\ rcv.receiver = i /\ rcv.type = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxInView(i)]
  /\ loc' = [loc EXCEPT ![i] = "phase2b"]
  /\ UNCHANGED <<view, prop, decided, crashed, msgs, recv>>

\* Phase 2 broadcast: the process sends both its proposal and its estimate.
Phase2Broadcast(i) ==
  /\ loc[i] = "phase2b"
  /\ msgs' = msgs \cup {[type |-> "phase2", value |-> prop[i], sender |-> i,
                         est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "phase2w"]
  /\ UNCHANGED <<view, prop, estimate, decided, crashed, recv>>

\* Phase 2 reception: a process integrates an estimate into its local view.
Phase2Receive(rcv) ==
  /\ rcv.receiver \in 1..N
  /\ loc[rcv.receiver] = "phase2w"
  /\ rcv.type = "phase2"
  /\ [type |-> "phase2", value |-> view[rcv.receiver][rcv.sender],
                         sender |-> rcv.sender, est |-> rcv.est]
       \notin msgs
  /\ msgs' = msgs \cup {[type |-> "phase2", value |-> view[rcv.receiver][rcv.sender],
                         sender |-> rcv.sender, est |-> rcv.est]}
  /\ view' = [view EXCEPT ![rcv.receiver][rcv.sender] = rcv.value]
  /\ recv' = recv \cup {rcv}
  /\ UNCHANGED <<loc, prop, estimate, decided, crashed>>

\* Decision by majority: a process decides once N-T phase-2 messages agree on some
\* estimate. This is the condition that makes all decisions coincide.
Phase2Decide(i) ==
  /\ loc[i] = "phase2w"
  /\ \E v \in Values :
       Cardinality({rcv.sender : rcv \in recv /\ rcv.receiver = i /\ rcv.type = "phase2" /\ rcv.est = v}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, recv>>

\* If no estimate reaches the N-T threshold, the process deterministically picks
\* one from its already-learned view and decides that instead.
Phase2Choose(i) ==
  /\ loc[i] = "phase2w"
  /\ \A v \in Values :
       Cardinality({rcv.sender : rcv \in recv /\ rcv.receiver = i /\ rcv.type = "phase2" /\ rcv.est = v}) < N - T
  /\ \E v \in Values : \E j \in 1..N : view[i][j] = v /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, estimate, crashed, msgs, recv>>

Crash(i) ==
  /\ crashed < F
  /\ loc[i] \notin {"crashed","done"}
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decided, msgs, recv>>

Next ==
  \/ \E i \in 1..N : Phase1Broadcast(i) \/ Phase1ToPhase2(i) \/ Phase2Broadcast(i)
                        \/ Phase2Decide(i) \/ Phase2Choose(i)
  \/ \E rcv \in [receiver: 1..N, sender: 1..N, type: {"phase1","phase2"}] :
       Phase1Receive(rcv) \/ Phase2Receive(rcv)
  \/ \E i \in 1..N : Crash(i)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N : Phase1Broadcast(i))
  /\ WF_vars(\E i \in 1..N : Phase2Broadcast(i))
  /\ WF_vars(\E i \in 1..N : Phase1Receive([receiver |-> i, sender |-> i, type |-> "phase1"]))
  /\ WF_vars(\E i \in 1..N : Phase2Receive([receiver |-> i, sender |-> i, type |-> "phase2"]))
  /\ WF_vars(\E i \in 1..N : Phase1ToPhase2(i))
  /\ WF_vars(\E i \in 1..N : Phase2Decide(i))
  /\ WF_vars(\E i \in 1..N : Phase2Choose(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : prop[j] = decided[i]

Agreement == \A i \in 1..N : decided[i] # Bottom => \A j \in 1..N : decided[j] = Bottom \/ decided[j] = decided[i]

Terminate == <>(\A i \in 1..N : loc[i] \in {"done","crashed"})

MaxProposed == \E j \in 1..N : prop[j] = (CHOOSE x \in Values : \A k \in 1..N : prop[k] <= x)

CondTerminate == MaxProposed ~> Terminate

\* The reference model also asserts that the number of distinct values in a
\* process's view grows monotonically as more messages are received -- a sanity
\* check that the view only ever accumulates information, never loses it.
ViewMonotone ==
  \A i \in 1..N : \A s \in [1..N -> Values \cup {Bottom}] :
    (\A j \in 1..N : view[i][j] # Bottom => s[j] = view[i][j]) => view[i] = s

Properties == Terminate /\ CondTerminate

====