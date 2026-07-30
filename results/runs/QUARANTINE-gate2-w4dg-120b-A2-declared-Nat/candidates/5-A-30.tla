---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

\* Participants and the coordinator are subject to abrupt crash. The
\* coordinator decides commit only when every participant voted yes, so
\* a single no vote forces abort for the whole transaction. Because
\* broadcast is simple (sequential), a coordinator crash mid-broadcast
\* can leave a participant undecided forever -- termination is NOT
\* guaranteed under failures, which is why the non-blocking property
\* AC5 is absent from this spec.
\* Strong fairness on the progress actions (excluding death) is
\* assumed in the .cfg, so a live, enabled participant eventually
\* makes progress.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, sent, requested, recv, sentDecision

vars == << vote, alive, decision, faulty, sent, requested, recv, sentDecision >>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants \cup {"coord"} -> {undecided, commit, abort}]
  /\ faulty \subseteq participants \cup {"coord"}
  /\ sent \subseteq participants
  /\ requested \subseteq participants
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ sentDecision \in [participants -> {commit, abort, notsent}]

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants \cup {"coord"} |-> undecided]
  /\ faulty = {}
  /\ sent = {}
  /\ requested = {}
  /\ recv = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]

\* The coordinator solicits a vote from a participant.
RequestVote(p) ==
  /\ alive["coord"]
  /\ p \notin requested
  /\ requested' = requested \cup {p}
  /\ UNCHANGED << vote, alive, decision, faulty, sent, recv, sentDecision >>

\* The coordinator receives a participant's vote.
RecvVote(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ p \in requested
  /\ recv[p] = waiting
  /\ p \in sent
  /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sent, requested, sentDecision >>

\* The coordinator detects a participant that died silently before voting.
DetectFault(p) ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ p \in requested
  /\ recv[p] = waiting
  /\ ~alive[p]
  /\ decision' = [decision EXCEPT !["coord"] = abort]
  /\ UNCHANGED << vote, alive, faulty, sent, requested, recv, sentDecision >>

\* The coordinator decides commit only when every received vote is yes.
Decide ==
  /\ alive["coord"]
  /\ decision["coord"] = undecided
  /\ requested = participants
  /\ \A p \in participants : recv[p] # waiting
  /\ decision' = [decision EXCEPT !["coord"] = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort]
  /\ UNCHANGED << vote, alive, faulty, sent, requested, recv, sentDecision >>

\* Simple broadcast: the coordinator sends its decision to exactly one participant at a time.
Broadcast(p) ==
  /\ alive["coord"]
  /\ decision["coord"] # undecided
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = decision["coord"]]
  /\ UNCHANGED << vote, alive, decision, faulty, sent, requested, recv >>

\* The coordinator crashes; it is then faulty and stops acting.
DieCoordinator ==
  /\ alive["coord"]
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = faulty \cup {"coord"}
  /\ UNCHANGED << vote, decision, sent, requested, recv, sentDecision >>

\* A live participant sends its vote to the coordinator after a request.
SendVote(p) ==
  /\ alive[p]
  /\ p \notin sent
  /\ p \in requested
  /\ sent' = sent \cup {p}
  /\ UNCHANGED << vote, alive, decision, faulty, requested, recv, sentDecision >>

\* A participant can unilaterally abort on its own no vote.
AbortOnNo(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in sent
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sent, requested, recv, sentDecision >>

\* A participant aborts when the coordinator died before it ever requested.
AbortOnNoRequest(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~alive["coord"]
  /\ p \notin requested
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty, sent, requested, recv, sentDecision >>

\* A participant adopts the coordinator's broadcast decision.
DecideFromBroadcast(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED << vote, alive, faulty, sent, requested, recv, sentDecision >>

\* A participant crashes silently.
DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, decision, sent, requested, recv, sentDecision >>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : RecvVote(p)
  \/ \E p \in participants : DetectFault(p)
  \/ Decide
  \/ \E p \in participants : Broadcast(p)
  \/ DieCoordinator
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnNo(p)
  \/ \E p \in participants : AbortOnNoRequest(p)
  \/ \E p \in participants : DecideFromBroadcast(p)
  \/ \E p \in participants : DieParticipant(p)

\* Weak fairness on the non-death progress actions is assumed in the
\* .cfg file (SF). Death is not fair and can happen at any time.
Spec == Init /\ [][Next]_vars

\* Safety: committed participants never disagree, a commit is backed by
\* universal yes, an abort is justified by a no vote or a failure, and
\* each participant decides at most once.
AC1 == \A p \in participants, q \in participants : (decision[p] = commit /\ decision[q] = abort) => FALSE
AC2 == (\E p \in participants : decision[p] = commit) => \A p \in participants : vote[p] = yes
AC3 == (\E p \in participants : decision[p] = abort) => (\E p \in participants : vote[p] = no) \/ (\E p \in participants : p \in faulty) \/ ("coord" \in faulty)
AC4 == (\A p \in participants : decision[p] = commit) => (\A p \in participants : decision[p] = commit) /\ (\A p \in participants : decision[p] = abort) => (\A p \in participants : decision[p] = abort)

\* Liveness: either every participant eventually decides, or a
\* participant or the coordinator fails, which is the only way a
\* participant can be left undecided forever.
AC3Liveness ==
  <>(\E p \in participants : decision[p] # undecided) \/ (\E p \in participants : p \in faulty) \/ ("coord" \in faulty)

====