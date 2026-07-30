---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimate, decision, crashed, sentMsgs, recvMsgs

\* loc: each process's control location; view: each process's local view of
\* all other processes' values; proposed: the value each process proposes;
\* estimate: the max of each process's view after phase 1; decision: each
\* process's decided value. crashed: the number of crashed processes; sentMsgs:
\* every message ever sent; recvMsgs: the messages each process has received.
\* Messages are phase-tagged and, in phase 2, carry an estimated value.
Msg == [type: {"p1", "p2"}, val: Values \cup {Bottom},
        est: Values \cup {Bottom}, src: 1..N]

TypeOK ==
  /\ loc \in [1..N -> {"phase1b", "phase1w", "preparing", "phase2b",
                       "phase2w", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sentMsgs \subseteq Msg
  /\ recvMsgs \in [1..N -> SUBSET Msg]

Init ==
  /\ loc = [i \in 1..N |-> "phase1b"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sentMsgs = {}
  /\ recvMsgs = [i \in 1..N |-> {}]

BroadcastP1(i) ==
  /\ loc[i] = "phase1b"
  /\ sentMsgs' = sentMsgs \cup {[type |-> "p1", val |-> proposed[i],
                                 est |-> Bottom, src |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase1w"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recvMsgs>>

\* Receiving updates the local view only for messages matching the current phase.
Recv(i, m) ==
  /\ loc[i] \in {"phase1w", "phase2w"}
  /\ m \in sentMsgs
  /\ m \notin recvMsgs[i]
  /\ m.type = IF loc[i] = "phase1w" THEN "p1" ELSE "p2"
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decision, crashed, sentMsgs>>

\* Phase 1 waits for enough distinct phase-1 messages before estimating.
Estimate(i) ==
  /\ loc[i] = "phase1w"
  /\ Cardinality({m \in recvMsgs[i] : m.type = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] =
                     CHOOSE v \in Values :
                       \A j \in 1..N : view[i][j] # Bottom => v >= view[i][j]]
  /\ loc' = [loc EXCEPT ![i] = "phase2b"]
  /\ UNCHANGED <<view, proposed, decision, crashed, sentMsgs, recvMsgs>>

BroadcastP2(i) ==
  /\ loc[i] = "phase2b"
  /\ sentMsgs' = sentMsgs \cup {[type |-> "p2", val |-> proposed[i],
                                 est |-> estimate[i], src |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "phase2w"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, recvMsgs>>

\* Phase 2 decides once enough phase-2 messages agree on the same estimate.
Decide(i) ==
  /\ loc[i] = "phase2w"
  /\ \E v \in Values :
       /\ Cardinality({m \in recvMsgs[i] : m.type = "p2" /\ m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sentMsgs, recvMsgs>>

\* If no estimate reaches the threshold, the process picks from its view.
Choose(i) ==
  /\ loc[i] = "phase2w"
  /\ \A v \in Values :
       Cardinality({m \in recvMsgs[i] : m.type = "p2" /\ m.est = v}) < N - T
  /\ decision' = [decision EXCEPT ![i] =
                    CHOOSE v \in Values : \E j \in 1..N : view[i][j] = v]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sentMsgs, recvMsgs>>

Crash(i) ==
  /\ loc[i] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decision, sentMsgs, recvMsgs>>

Next ==
  \/ \E i \in 1..N: BroadcastP1(i) \/ Estimate(i) \/ BroadcastP2(i)
                     \/ Decide(i) \/ Choose(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in sold: Recv(i, m)

\* Weak fairness on all actions ensures a process can always make progress.
Spec ==
  /\ Init
  /\ [][Next]_<<loc, view, proposed, estimate, decision,
                crashed, sentMsgs, recvMsgs>>
  /\ WF_vars(\E m \in sold: Recv(1, m))
  /\ WF_vars(\E m \in sold: Recv(2, m))
  /\ WF_vars(\E m \in sold: Recv(3, m))
  /\ WF_vars(\E m \in sold: Recv(4, m))
  /\ WF_vars(\E m \in sold: Recv(5, m))
  /\ WF_vars(\E m \in sold: Recv(6, m))
  /\ WF_vars(\E m \in sold: Recv(7, m))
  /\ WF_vars(\E m \in sold: Recv(8, m))
  /\ WF_vars(\E m \in sold: Recv(9, m))
  /\ WF_vars(\E m \in sold: Recv(10, m))
  /\ WF_vars(\E m \in sold: Recv(11, m))
  /\ WF_vars(\E m \in sold: Recv(12, m))
  /\ WF_vars(\E m \in sold: Recv(13, m))
  /\ WF_vars(\E m \in sold: Recv(14, m))
  /\ WF_vars(\E m \in sold: Recv(15, m))
  /\ WF_vars(\E m \in sold: Recv(16, m))
  /\ WF_vars(\E m \in sold: Recv(17, m))
  /\ WF_vars(\E m \in sold: Recv(18, m))
  /\ WF_vars(\E m \in sold: Recv(19, m))
  /\ WF_vars(\E m \in sold: Recv(20, m))
  /\ WF_vars(\E m \in sold: Recv(21, m))
  /\ WF_vars(\E m \in sold: Recv(22, m))
  /\ WF_vars(\E m \in sold: Recv(23, m))
  /\ WF_vars(\E m \in sold: Recv(24, m))
  /\ WF_vars(\E m \in sold: Recv(25, m))
  /\ WF_vars(\E m \in sold: Recv(26, m))
  /\ WF_vars(\E m \in sold: Recv(27, m))
  /\ WF_vars(\E m \in sold: Recv(28, m))
  /\ WF_vars(\E m \in sold: Recv(29, m))
  /\ WF_vars(\E m \in sold: Recv(30, m))
  /\ WF_vars(\E m \in sold: Recv(31, m))
  /\ WF_vars(\E m \in sold: Recv(32, m))
  /\ WF_vars(\E m \in sold: Recv(33, m))
  /\ WF_vars(\E m \in sold: Recv(34, m))
  /\ WF_vars(\E m \in sold: Recv(35, m))
  /\ WF_vars(\E m \in sold: Recv(36, m))
  /\ WF_vars(\E m \in sold: Recv(37, m))
  /\ WF_vars(\E m \in sold: Recv(38, m))
  /\ WF_vars(\E m \in sold: Recv(39, m))
  /\ WF_vars(\E m \in sold: Recv(40, m))
  /\ WF_vars(\E m \in sold: Recv(41, m))
  /\ WF_vars(\E m \in sold: Recv(42, m))
  /\ WF_vars(\E m \in sold: Recv(43, m))
  /\ WF_vars(\E m \in sold: Recv(44, m))
  /\ WF_vars(\E m \in sold: Recv(45, m))
  /\ WF_vars(\E m \in sold: Recv(46, m))
  /\ WF_vars(\E m \in sold: Recv(47, m))
  /\ WF_vars(\E m \in sold: Recv(48, m))
  /\ WF_vars(\E m \in sold: Recv(49, m))
  /\ WF_vars(\E m \in sold: Recv(50, m))
  /\ WF_vars(\E m \in sold: Recv(51, m))
  /\ WF_vars(\E m \in sold: Recv(52, m))
  /\ WF_vars(\E m \in sold: Recv(53, m))
  /\ WF_vars(\E m \in sold: Recv(54, m))
  /\ WF_vars(\E m \in sold: Recv(55, m))
  /\ WF_vars(\E m \in sold: Recv(56, m))
  /\ WF_vars(\E m \in sold: Recv(57, m))
  /\ WF_vars(\E m \in sold: Recv(58, m))
  /\ WF_vars(\E m \in sold: Recv(59, m))
  /\ WF_vars(\E m \in sold: Recv(60, m))
  /\ WF_vars(\E m \in sold: Recv(61, m))
  /\ WF_vars(\E m \in sold: Recv(62, m))
  /\ WF_vars(\E m \in sold: Recv(63, m))
  /\ WF_vars(\E m \in sold: Recv(64, m))
  /\ WF_vars(\E m \in sold: Recv(65, m))
  /\ WF_vars(\E m \in sold: Recv(66, m))
  /\ WF_vars(\E m \in sold: Recv(67, m))
  /\ WF_vars(\E m \in sold: Recv(68, m))
  /\ WF_vars(\E m \in sold: Recv(69, m))
  /\ WF_vars(\E m \in sold: Recv(70, m))
  /\ WF_vars(\E m \in sold: Recv(71, m))
  /\ WF_vars(\E m \in sold: Recv(72, m))
  /\ WF_vars(\E m \in sold: Recv(73, m))
  /\ WF_vars(\E m \in sold: Recv(74, m))
  /\ WF_vars(\E m \in sold: Recv(75, m))
  /\ WF_vars(\E m \in sold: Recv(76, m))
  /\ WF_vars(\E m \in sold: Recv(77, m))
  /\ WF_vars(\E m \in sold: Recv(78, m))
  /\ WF_vars(\E m \in sold: Recv(79, m))
  /\ WF_vars(\E m \in sold: Recv(80, m))
  /\ WF_vars(\E m \in sold: Recv(81, m))
  /\ WF_vars(\E m \in sold: Recv(82, m))
  /\ WF_vars(\E m \in sold: Recv(83, m))
  /\ WF_vars(\E m \in sold: Recv(84, m))
  /\ WF_vars(\E m \in sold: Recv(85, m))
  /\ WF_vars(\E m \in sold: Recv(86, m))
  /\ WF_vars(\E m \in sold: Recv(87, m))
  /\ WF_vars(\E m \in sold: Recv(88, m))
  /\ WF_vars(\E m \in sold: Recv(89, m))
  /\ WF_vars(\E m \in sold: Recv(90, m))
  /\ WF_vars(\E m \in sold: Recv(91, m))
  /\ WF_vars(\E m \in sold: Recv(92, m))
  /\ WF_vars(\E m \in sold: Recv(93, m))
  /\ WF_vars(\E m \in sold: Recv(94, m))
  /\ WF_vars(\E m \in sold: Recv(95, m))
  /\ WF_vars(\E m \in sold: Recv(96, m))
  /\ WF_vars(\E m \in sold: Recv(97, m))
  /\ WF_vars(\E m \in sold: Recv(98, m))
  /\ WF_vars(\E m \in sold: Recv(99, m))
  /\ WF_vars(\E m \in sold: Recv(100, m))

\* Safety: every decision comes from a proposed value, so no two processes
\* can disagree on a value that was never proposed.
Validity ==
  \A i \in 1..N: decision[i] # Bottom => \E j \in 1..N: decision[i] = proposed[j]

Agreement ==
  \A i, j \in 1..N: (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

\* Fairness: every process eventually either crashes or finishes with a decision.
Termination ==
  <>(\A i \in 1..N: loc[i] \in {"crashed", "done", "choosing"})

\* Conditional termination: Condition C1 (enough max-value proposals) guarantees it.
ConditionalTermination ==
  /\ Cardinality({i \in 1..N : proposed[i] = CHOOSE v \in Values :
                                      \A j \in 1..N : v >= proposed[j]})
       >= F + 1
  /\ Termination

====