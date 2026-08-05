---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES vote, alive, decision, faulty, requested, coordinatorDecision, sentDecision

vars == <<vote, alive, decision, faulty, requested, coordinatorDecision, sentDecision>>

\* Simple broadcast: the coordinator sends a decision message to each participant one at
\* a time, so a coordinator failure during broadcast can strand a participant undecided.
\* Failure detection here is "magical" (immediate), not timeout-based, to focus on the
\* commit protocol itself rather than on the mechanics of crash detection.

RECURSIVE AllVoted(_)
AllVoted(S) ==
  \/ S = {}
  \/ \E p \in S : coordinatorDecision[p] # waiting /\ AllVoted(S \ {p})

RECURSIVE AllCommitted(_)
AllCommitted(S) ==
  \/ S = {}
  \/ \E p \in S : decision[p] = commit /\ AllCommitted(S \ {p})

RECURSIVE AnyAborted(_)
AnyAborted(S) ==
  \/ \E p \in S : decision[p] = abort
  \/ \E p \in S : AnyAborted(S \ {p})

RECURSIVE SomeSentDecision(_)
SomeSentDecision(S) ==
  \/ \E p \in S : sentDecision[p] # notsent \/ SomeSentDecision(S \ {p})
  \/ S = {}

RECURSIVE AllSentDecision(_)
AllSentDecision(S) ==
  \/ S = {}
  \/ \E p \in S : sentDecision[p] = coordinatorDecision[p] /\ AllSentDecision(S \ {p})

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants \cup {"coord"} -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants \cup {"coord"}
  /\ requested \subseteq participants
  /\ coordinatorDecision \in [participants -> {waiting, commit, abort}]
  /\ sentDecision \in [participants -> {notsent, commit, abort}]

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants \cup {"coord"} |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ requested = {}
  /\ coordinatorDecision = [p \in participants |-> waiting]
  /\ sentDecision = [p \in participants |-> notsent]

\* Coordinator actions
RequestVote(p) ==
  /\ "coord" \in alive
  /\ p \notin requested
  /\ requested' = requested \cup {p}
  /\ UNCHANGED <<vote, alive, decision, faulty, coordinatorDecision, sentDecision>>

ReceiveVote(p) ==
  /\ "coord" \in alive
  /\ coordinatorDecision[p] = waiting
  /\ p \in requested
  /\ p \notin faulty
  /\ coordinatorDecision' = [coordinatorDecision EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, sentDecision>>

CoordinatorDetectFault(p) ==
  /\ "coord" \in alive
  /\ coordinatorDecision[p] = waiting
  /\ p \in requested
  /\ p \notin alive
  /\ coordinatorDecision' = [coordinatorDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, sentDecision>>

Decide ==
  /\ "coord" \in alive
  /\ coordinatorDecision' = [p \in participants |-> IF AllVoted(participants) THEN IF \A q \in participants : vote[q] = yes THEN commit ELSE abort ELSE coordinatorDecision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, sentDecision>>

BroadcastDecision(p) ==
  /\ "coord" \in alive
  /\ coordinatorDecision[p] # waiting
  /\ sentDecision[p] = notsent
  /\ sentDecision' = [sentDecision EXCEPT ![p] = coordinatorDecision[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, coordinatorDecision>>

DieCoordinatort ==
  /\ "coord" \in alive
  /\ alive' = [alive EXCEPT !["coord"] = FALSE]
  /\ faulty' = faulty \cup {"coord"}
  /\ UNCHANGED <<vote, decision, requested, coordinatorDecision, sentDecision>>

\* Participant actions
SendVote(p) ==
  /\ p \in alive
  /\ p \in requested
  /\ coordinatorDecision[p] = waiting
  /\ coordinatorDecision' = [coordinatorDecision EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, requested, sentDecision>>

AbortOnVote(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ vote[p] = no
  /\ coordinatorDecision[p] = waiting
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, requested, coordinatorDecision, sentDecision>>

AbortOnTimeout(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ coordinatorDecision[p] = waiting
  /\ "coord" \notin alive
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, requested, coordinatorDecision, sentDecision>>

DecideFromCoordinator(p) ==
  /\ p \in alive
  /\ decision[p] = undecided
  /\ sentDecision[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = sentDecision[p]]
  /\ UNCHANGED <<vote, alive, faulty, requested, coordinatorDecision, sentDecision>>

DieParticipantt(p) ==
  /\ p \in alive
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED <<vote, decision, requested, coordinatorDecision, sentDecision>>

Next ==
  \/ \E p \in participants : RequestVote(p)
  \/ \E p \in participants : ReceiveVote(p)
  \/ \E p \in participants : CoordinatorDetectFault(p)
  \/ Decide
  \/ \E p \in participants : BroadcastDecision(p)
  \/ DieCoordinatort
  \/ \E p \in participants : SendVote(p)
  \/ \E p \in participants : AbortOnVote(p)
  \/ \E p \in participants : AbortOnTimeout(p)
  \/ \E p \in participants : DecideFromCoordinator(p)
  \/ \E p \in participants : DieParticipantt(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Decide)
  /\ WF_vars(\E p \in participants : RequestVote(p))
  /\ WF_vars(\E p \in participants : ReceiveVote(p))
  /\ WF_vars(\E p \in participants : AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))

\* Consistency: no two participants ever disagree on the outcome.
Agreement ==
  ~ \E p1 \in participants, p2 \in participants :
       decision[p1] = commit /\ decision[p2] = abort

\* A commit can only happen if every vote was yes.
CommitValidity ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* An abort must be traceable to a no vote, a participant crash, or a coordinator crash.
AbortValidity ==
  (\E p \in participants : decision[p] = abort) =>
    (\E p \in participants : vote[p] = no) \/ (\E p \in participants : p \in faulty) \/ ("coord" \in faulty)

Irrevocability ==
  /\ (\E p \in participants : decision[p] = commit) => AllCommitted(participants)
  /\ (\E p \in participants : decision[p] = abort) => ~AnyAborted(participants)

\* Because broadcast is simple (one message at a time) and the coordinator can fail,
\* the protocol can stall with some participants undecided -- termination is not
\* guaranteed. What is guaranteed is that the system always makes progress in some
\* direction: all participants eventually decide, or a failure is discovered.
Termination ==
  <>(\A p \in participants : decision[p] # undecided \/ p \in faulty \/ "coord" \in faulty)

====