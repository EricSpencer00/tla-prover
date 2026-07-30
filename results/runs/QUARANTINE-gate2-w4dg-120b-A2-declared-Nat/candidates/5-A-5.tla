---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS
  participants, yes, no, undecided, commit, abort,
  waiting, notsent

VARIABLES
  vote, alive, decision, faulty, sent,
  requestSent, recv, broadcast, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent,
           requestSent, recv, broadcast, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in BOOLEAN
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \in BOOLEAN
  /\ sent \in [participants -> BOOLEAN]
  /\ requestSent \in [participants -> BOOLEAN]
  /\ recv \in [participants -> {yes, no, waiting}]
  /\ broadcast \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = TRUE
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = FALSE
  /\ sent = [p \in participants |-> FALSE]
  /\ requestSent = [p \in participants |-> FALSE]
  /\ recv = [p \in participants |-> waiting]
  /\ broadcast = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator actions:

\* 1. Broadcast a vote request to a participant.
RequestVote(p) ==
  /\ coordAlive = TRUE
  /\ requestSent[p] = FALSE
  /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* 2. Receive a vote from the participant.
ReceiveVote(p) ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ requestSent[p] = TRUE
  /\ recv[p] = waiting
  /\ sent[p] = TRUE
  /\ recv' = [recv EXCEPT ![p] = vote[p]]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 requestSent, broadcast, coordDecision,
                 coordAlive, coordFaulty>>

\* 3. Detect a participant fault and decide abort.
DetectFault(p) ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ requestSent[p] = TRUE
  /\ recv[p] = waiting
  /\ sent[p] = FALSE
  /\ coordDecision' = abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 requestSent, recv, broadcast, coordAlive, coordFaulty>>

\* 4. Make the commit or abort decision once every vote is collected.
DecideNow ==
  /\ coordAlive = TRUE
  /\ coordDecision = undecided
  /\ \A p \in participants : recv[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recv[p] = yes THEN commit ELSE abort
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 requestSent, recv, broadcast, coordAlive, coordFaulty>>

\* 5. Broadcast the decision to a participant (simple broadcast: one participant
\*    at a time, which can be interrupted by a coordinator crash).
BroadcastDecision(p) ==
  /\ coordAlive = TRUE
  /\ coordDecision # undecided
  /\ broadcast[p] = notsent
  /\ broadcast' = [broadcast EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 requestSent, recv, coordDecision, coordAlive, coordFaulty>>

\* 6. The coordinator crashes.
DieCoordinator ==
  /\ coordAlive = TRUE
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<vote, alive, decision, faulty, sent,
                 requestSent, recv, broadcast, coordDecision>>

\* Participant actions:

\* 1. Send your vote to the coordinator.
SendVote(p) ==
  /\ alive = TRUE
  /\ requestSent[p] = TRUE
  /\ sent[p] = FALSE
  /\ sent' = [sent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<vote, decision, faulty, requestSent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* 2. Abort unilaterally if your vote is no.
AbortOnNo(p) ==
  /\ alive = TRUE
  /\ decision[p] = undecided
  /\ sent[p] = TRUE
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, requestSent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* 3. Abort on timeout because the coordinator died without requesting.
AbortOnCoordinatorGone(p) ==
  /\ alive = TRUE
  /\ decision[p] = undecided
  /\ coordAlive = FALSE
  /\ requestSent[p] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED <<vote, alive, faulty, sent, requestSent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* 4. Decide based on the coordinator's broadcast.
DecideFromCoordinator(p) ==
  /\ alive = TRUE
  /\ decision[p] = undecided
  /\ broadcast[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcast[p]]
  /\ UNCHANGED <<vote, alive, faulty, sent, requestSent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* 5. Crash.
Die(p) ==
  /\ alive = TRUE
  /\ alive' = FALSE
  /\ faulty' = TRUE
  /\ UNCHANGED <<vote, decision, sent, requestSent,
                 recv, broadcast, coordDecision, coordAlive, coordFaulty>>

\* Weak fairness: progress actions fire eventually when enabled; death actions are
\* not fair (they can strike at any moment).
Next ==
  \/ \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ DetectFault(p)
                              \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnNo(p)
                              \/ AbortOnCoordinatorGone(p) \/ DecideFromCoordinator(p)
                              \/ Die(p)
  \/ DecideNow
  \/ DieCoordinator

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnNo(p))
  /\ WF_vars(\E p \in participants : AbortOnCoordinatorGone(p))
  /\ WF_vars(\E p \in participants : DecideFromCoordinator(p))
  /\ WF_vars(\E p \in participants : RequestVote(p))
  /\ WF_vars(\E p \in participants : ReceiveVote(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))

\* No two participants decide differently.
Agreement ==
  \A p, q \in participants :
     (decision[p] = commit) => (decision[q] # abort)

\* Commit is only possible if everyone voted yes.
CommitValid ==
  \A p \in participants : decision[p] = commit => \A q \in participants : vote[q] = yes

\* Abort is justified only by a no vote or a crash.
AbortValid ==
  \A p \in participants : decision[p] = abort =>
    \/ \E q \in participants : vote[q] = no
    \/ faulty
    \/ coordFaulty

\* Each participant decides at most once.
DecideOnce ==
  \A p \in participants :
     /\ (decision[p] = commit) ~> (decision[p] = commit)
     /\ (decision[p] = abort) ~> (decision[p] = abort)

\* A non-blocking outcome is NOT guaranteed under simple broadcast: a crash
\* may leave the system undecided. The liveness condition therefore accepts
\* a decision having been reached, or any participant or coordinator crashing.
SomeDecisionOrCrash ==
  <>(\A p \in participants : decision[p] # undecided \/ faulty \/ coordFaulty)

====