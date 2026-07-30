---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Type checking without typed constants: values are distinguished by name, not type.
VARIABLES vote, alive, decided, faulty, sentVote,
         reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decided, faulty, sentVote,
           reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decided \in [participants -> {undecided, commit, abort}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ sentVote \in [participants -> BOOLEAN]
  /\ reqSentTo \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcastTo \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {commit, abort, undecided}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decided = [p \in participants |-> undecided]
  /\ faulty = [p \in participants |-> FALSE]
  /\ sentVote = [p \in participants |-> FALSE]
  /\ reqSentTo = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcastTo = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant.
SendRequest(p) ==
  /\ coordAlive
  /\ ~reqSentTo[p]
  /\ reqSentTo' = [reqSentTo EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a participant's vote (the vote arrives only once the
\* participant has already sent it).
RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSentTo[p]
  /\ recvVote[p] = waiting
  /\ sentVote[p]
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                reqSentTo, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* Failure detection: the coordinator notices a participant that has died
\* without sending its vote. This is a magical detection, not a timeout.
DetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSentTo[p]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordAlive, coordFaulty>>

\* With all votes received the coordinator decides commit or abort.
MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: recvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants: recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordAlive, coordFaulty>>

\* Simple broadcast: the coordinator sends its decision to one participant at a time.
BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcastTo[p] = notsent
  /\ broadcastTo' = [broadcastTo EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                reqSentTo, recvVote, coordDecision, coordAlive, coordFaulty>>

\* The coordinator dies; this is not weakly fair.
DieCoordinator ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decided, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordFaulty>>

\* A participant sends its vote to the coordinator.
SendVote(p) ==
  /\ alive[p]
  /\ reqSentTo[p]
  /\ ~sentVote[p]
  /\ sentVote' = [sentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decided, faulty,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* A participant decides abort on its own because it voted no.
AbortOnVote(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ sentVote[p]
  /\ vote[p] = no
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* A participant aborts because the coordinator died before sending a request.
AbortOnTimeout(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ ~coordAlive
  /\ ~reqSentTo[p]
  /\ decided' = [decided EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* A participant adopts the coordinator's broadcasted decision.
DecideOnBroadcast(p) ==
  /\ alive[p]
  /\ decided[p] = undecided
  /\ broadcastTo[p] # notsent
  /\ decided' = [decided EXCEPT ![p] = broadcastTo[p]]
  /\ UNCHANGED <<vote, alive, faulty, sentVote,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* A participant dies; this is not weakly fair.
DieParticipant(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ faulty' = [faulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decided, sentVote,
                reqSentTo, recvVote, broadcastTo, coordDecision, coordAlive, coordFaulty>>

\* Stuttering for deadlock avoidance when the coordinator is dead.
Stall ==
  /\ ~coordAlive
  /\ \A p \in participants: ~alive[p]
  /\ UNCHANGED vars

Next ==
  \/ \E p \in participants: SendRequest(p)
  \/ \E p \in participants: RecvVote(p)
  \/ \E p \in participants: DetectFault(p)
  \/ MakeDecision
  \/ \E p \in participants: BroadcastDecision(p)
  \/ DieCoordinator
  \/ \E p \in participants: SendVote(p)
  \/ \E p \in participants: AbortOnVote(p)
  \/ \E p \in participants: AbortOnTimeout(p)
  \/ \E p \in participants: DecideOnBroadcast(p)
  \/ \E p \in participants: DieParticipant(p)
  \/ Stall

\* Weak fairness: progress actions tend to happen if enabled; death actions do not.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants: SendRequest(p))
  /\ WF_vars(\E p \in participants: RecvVote(p))
  /\ WF_vars(\E p \in participants: DetectFault(p))
  /\ WF_vars(\E p \in participants: SendVote(p))
  /\ WF_vars(\E p \in participants: AbortOnVote(p))
  /\ WF_vars(\E p \in participants: AbortOnTimeout(p))
  /\ WF_vars(\E p \in participants: DecideOnBroadcast(p))
  /\ WF_vars(\E p \in participants: DieParticipant(p))

\* Safety: no two participants can decide differently.
Agreement ==
  \A p, q \in participants:
    (decided[p] = commit /\ decided[q] = abort) => FALSE

\* If anybody decides commit, everybody voted yes.
CommitValidity ==
  (\E p \in participants: decided[p] = commit) => (\A q \in participants: vote[q] = yes)

\* If anybody decides abort, it is justified by a no vote or a failure.
AbortValidity ==
  (\E p \in participants: decided[p] = abort) =>
    (\E q \in participants: vote[q] = no) \/ (\E q \in participants: faulty[q]) \/ coordFaulty

\* Once a participant decides, it never decides again.
Irrevocability ==
  \A p \in participants:
    /\ decided[p] = commit => decided' = [decided EXCEPT ![p] = commit]
    /\ decided[p] = abort => decided' = [decided EXCEPT ![p] = abort]

\* Eventual resolution or failure: this is the intended outcome, not termination.
EventualResolution ==
  (\A p \in participants: decided[p] # undecided) \/ (\E p \in participants: faulty[p]) \/ coordFaulty

====