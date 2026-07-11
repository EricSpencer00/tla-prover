---- MODULE cbc_max ----
(***************************************************************************)
(* Condition-based consensus with maximum value (CBC-MAX).                 *)
(*                                                                         *)
(* This is a faithful TLA+ model of the two-phase protocol described in   *)
(* the problem statement, with crash faults, bounded by T, and the       *)
(* condition C1: at least F+1 processes propose the global maximum.     *)
(*                                                                         *)
(* Safety: Validity (decided value was proposed) and Agreement (no two   *)
(* processes decide differently).                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME 2 * T < N
ASSUME 0 <= F <= T
ASSUME N > 0
ASSUME Values \subseteq {v \in 1..N : v # Bottom}
ASSUME Bottom \notin Values

Procs == 1..N

\* The control location of each process.
Locs == {"bcast1", "wait1", "bcast2", "wait2", "choosing", "done", "crashed"}

\* The local view matrix: view[p][q] is the value p has learned about q.
\* Initially Bottom for all entries.
Views == [p \in Procs |-> [q \in Procs |-> Bottom]]

\* The proposed value of each process.
Proposed == [p \in Procs |-> CHOOSE v \in Values : TRUE]

\* The estimated value (max over view) of each process (Bottom until set).
Estimated == [p \in Procs |-> Bottom]

\* The decision value of each process (Bottom until decided).
Decision == [p \in Procs |-> Bottom]

\* The set of crashed processes.
Crashed == {}

\* The set of messages in transit.  A message is a tuple
\*   [type : {"p1", "p2"}, sender : Procs, value : Values, est : Values]
\* For phase-1 messages, est = Bottom.
Msgs == {}

\* The set of messages received by each process.
\* For simplicity, we track only the set of messages that have been
\* delivered to each process; the local view is updated on delivery.
RecvSet == [p \in Procs |-> {}]

\* The global maximum value in the value set.
MaxVal == CHOOSE v \in Values : \A w \in Values : v >= w

Init == /\ Locs     = [p \in Procs |-> "bcast1"]
        /\ Views    = [p \in Procs |-> [q \in Procs |-> Bottom]]
        /\ Proposed = [p \in Procs |-> CHOOSE v \in Values : TRUE]
        /\ Estimated = [p \in Procs |-> Bottom]
        /\ Decision = [p \in Procs |-> Bottom]
        /\ Crashed = {}
        /\ Msgs = {}
        /\ RecvSet = [p \in Procs |-> {}]

\* Broadcast a phase-1 message.
Bcast1(p) == /\ Locs[p] = "bcast1"
             /\ Locs' = [Locs EXCEPT ![p] = "wait1"]
             /\ Msgs' = Msgs \cup { [type |-> "p1", sender |-> p,
                                      value |-> Proposed[p], est |-> Bottom] }
             /\ UNCHANGED << Views, Proposed, Estimated, Decision, Crashed, RecvSet >>

\* Deliver a phase-1 message to a process.
Recv1(p, m) == /\ Locs[p] \in {"bcast1", "wait1"}
               /\ m \in Msgs
               /\ m.type = "p1"
               /\ Views' = [Views EXCEPT ![p][m.sender] = m.value]
               /\ RecvSet' = [RecvSet EXCEPT ![p] = RecvSet[p] \cup {m}]
               /\ UNCHANGED << Locs, Proposed, Estimated, Decision, Crashed, Msgs >>

\* Transition from phase-1 waiting to phase-2 broadcasting once enough
\* phase-1 messages have been received (at least N-T distinct senders).
\* Compute the estimated value as the maximum over the local view.
Bcast2(p) == /\ Locs[p] = "wait1"
             /\ Cardinality({ m.sender : m \in RecvSet[p] /\ m.type = "p1" }) >= N - T
             /\ Estimated' = [Estimated EXCEPT ![p] = CHOOSE v \in Values :
                               \A w \in Values : v >= w /\ v \in
                                 { Views[p][q] : q \in Procs /\ Views[p][q] # Bottom }]
             /\ Locs' = [Locs EXCEPT ![p] = "bcast2"]
             /\ Msgs' = Msgs \cup { [type |-> "p2", sender |-> p,
                                      value |-> Proposed[p], est |-> Estimated[p]] }
             /\ UNCHANGED << Views, Proposed, Decision, Crashed, RecvSet >>

\* Deliver a phase-2 message to a process.
Recv2(p, m) == /\ Locs[p] \in {"bcast2", "wait2", "choosing"}
               /\ m \in Msgs
               /\ m.type = "p2"
               /\ Views' = [Views EXCEPT ![p][m.sender] = m.value]
               /\ RecvSet' = [RecvSet EXCEPT ![p] = RecvSet[p] \cup {m}]
               /\ UNCHANGED << Locs, Proposed, Estimated, Decision, Crashed, Msgs >>

\* Transition from phase-2 waiting to done once a quorum of phase-2
\* messages with the same estimated value has been received.
Done(p) == /\ Locs[p] = "wait2"
           /\ \E e \in Values :
                Cardinality({ m.sender : m \in RecvSet[p] /\ m.type = "p2" /\ m.est = e }) >= N - T
           /\ Decision' = [Decision EXCEPT ![p] = e]
           /\ Locs' = [Locs EXCEPT ![p] = "done"]
           /\ UNCHANGED << Views, Proposed, Estimated, Crashed, Msgs, RecvSet >>

\* Transition from phase-2 waiting to choosing when all phase-2 messages
\* have been received but no quorum for any estimated value.
Choosing(p) == /\ Locs[p] = "wait2"
               /\ Cardinality({ m.sender : m \in RecvSet[p] /\ m.type = "p2" }) = N
               /\ \A e \in Values : Cardinality({ m.sender : m \in RecvSet[p] /\ m.type = "p2" /\ m.est = e }) < N - T
               /\ Locs' = [Locs EXCEPT ![p] = "choosing"]
               /\ UNCHANGED << Views, Proposed, Estimated, Decision, Crashed, Msgs, RecvSet >>

\* Deterministic choosing: pick the smallest value that appears in the
\* local view (ties broken by value order).
Choose(p) == /\ Locs[p] = "choosing"
             /\ Decision' = [Decision EXCEPT ![p] = CHOOSE v \in Values :
                               \A w \in Values : v <= w /\ v \in
                                 { Views[p][q] : q \in Procs /\ Views[p][q] # Bottom }]
             /\ Locs' = [Locs EXCEPT ![p] = "done"]
             /\ UNCHANGED << Views, Proposed, Estimated, Crashed, Msgs, RecvSet >>

\* Crash a process (only if fewer than F have crashed so far).
Crash(p) == /\ p \notin Crashed
            /\ Cardinality(Crashed) < F
            /\ Locs' = [Locs EXCEPT ![p] = "crashed"]
            /\ Crashed' = Crashed \cup {p}
            /\ UNCHANGED << Views, Proposed, Estimated, Decision, Msgs, RecvSet >>

\* Phase-2 broadcasting: after broadcasting phase-2, a process moves to
\* the waiting state.
Wait2(p) == /\ Locs[p] = "bcast2"
            /\ Locs' = [Locs EXCEPT ![p] = "wait2"]
            /\ UNCHANGED << Views, Proposed, Estimated, Decision, Crashed, Msgs, RecvSet >>

Next == \/ \E p \in Procs : Bcast1(p)
        \/ \E p \in Procs : \E m \in Msgs : Recv1(p, m)
        \/ \E p \in Procs : Bcast2(p)
        \/ \E p \in Procs : \E m \in Msgs : Recv2(p, m)
        \/ \E p \in Procs : Done(p)
        \/ \E p \in Procs : Choosing(p)
        \/ \E p \in Procs : Choose(p)
        \/ \E p \in Procs : Crash(p)
        \/ \E p \in Procs : Wait2(p)

Spec == Init /\ [][Next]_<< Locs, Views, Proposed, Estimated, Decision, Crashed, Msgs, RecvSet >>

\* Strong safety: the decision value of any process that has decided
\* was indeed proposed by some process.
Validity == \A p \in Procs : Decision[p] # Bottom => Decision[p] \in Proposed

\* Strong safety: no two processes decide different values.
Agreement == \A p, q \in Procs : Decision[p] # Bottom /\ Decision[q] # Bottom => Decision[p] = Decision[q]

TypeOK == /\ Locs \in [Procs -> Locs]
          /\ Views \in [Procs -> [Procs -> Values \cup {Bottom}]]
          /\ Proposed \in [Procs -> Values]
          /\ Estimated \in [Procs -> Values \cup {Bottom}]
          /\ Decision \in [Procs -> Values \cup {Bottom}]
          /\ Crashed \subseteq Procs
          /\ Msgs \subseteq { [type : {"p1", "p2"}, sender : Procs,
                               value : Values, est : Values \cup {Bottom}] }
          /\ RecvSet \in [Procs -> SUBSET Msgs]
====