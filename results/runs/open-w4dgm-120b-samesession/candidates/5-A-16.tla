---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB) from            *)
(* Babaoglu & Toueg.  One coordinator collects votes from participants      *)
(* and broadcasts a commit/abort decision.  The simple broadcast can leave    *)
(* participants undecided if the coordinator crashes mid-broadcast.          *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Alive/coordinating: a participant/coordinator can crash (die) silently
\* at any time.  Simple broadcast: the coordinator sends its decision to
\* participants one at a time; a crash during this is what can block final
\* consensus, even though no participant ever lies about its vote.

VARIABLES vote, alive, decision, faulty, sent, coordSent, recvd,
          coordBroadcast, coordDecision, coordAlive, coordFaulty

vars == <<vote, alive, decision, faulty, sent, coordSent, recvd,
           coordBroadcast, coordDecision, coordAlive, coordFaulty>>

TypeOK ==
    /\ vote \in [participants -> {yes, no}]
    /\ alive \in [participants -> BOOLEAN]
    /\ decision \in [participants -> {undecided, commit, abort}]
    /\ faulty \in [participants -> BOOLEAN]
    /\ sent \in [participants -> BOOLEAN]
    /\ coordSent \in [participants -> BOOLEAN]
    /\ recvd \in [participants -> {yes, no, waiting}]
    /\ coordBroadcast \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ \E v \in [participants -> {yes, no}]:
         vote = v
    /\ alive = [p \in participants |-> TRUE]
    /\ decision = [p \in participants |-> undecided]
    /\ faulty = [p \in participants |-> FALSE]
    /\ sent = [p \in participants |-> FALSE]
    /\ coordSent = [p \in participants |-> FALSE]
    /\ recvd = [p \in participants |-> waiting]
    /\ coordBroadcast = [p \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator sends a vote request to a participant.
SendVoteRequest(p) ==
    /\ coordAlive
    /\ ~coordSent[p]
    /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, recvd,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Coordinator receives a vote from a participant that has sent it.
ReceiveVote(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ recvd[p] = waiting
    /\ sent[p]
    /\ recvd' = [recvd EXCEPT ![p] = vote[p]]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Coordinator detects a participant failure (no vote yet) and aborts.
DetectFault(p) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordSent[p]
    /\ recvd[p] = waiting
    /\ ~alive[p]
    /\ coordDecision' = abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordAlive, coordFaulty>>

\* Coordinator makes a decision once every vote has been received.
MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A p \in participants: recvd[p] # waiting
    /\ coordDecision' = IF \A p \in participants: recvd[p] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordAlive, coordFaulty>>

\* Coordinator broadcasts its decision to a participant (simple broadcast).
Broadcast(p) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcast[p] = notsent
    /\ coordBroadcast' = [coordBroadcast EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   recvd, coordDecision, coordAlive, coordFaulty>>

\* Coordinator crashes silently.
DieCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<vote, alive, decision, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordDecision>>

\* Participant sends its vote to the coordinator.
SendVote(p) ==
    /\ alive[p]
    /\ ~sent[p]
    /\ coordSent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, alive, decision, faulty,
                   coordSent, recvd, coordBroadcast, coordDecision,
                   coordAlive, coordFaulty>>

\* A participant that voted no aborts unilaterally.
AbortNo(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ sent[p]
    /\ vote[p] = no
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant times out waiting for a vote request because the
\* coordinator died; it aborts unilaterally.
AbortReqTimeout(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordAlive = FALSE
    /\ coordSent[p] = FALSE
    /\ decision' = [decision EXCEPT ![p] = abort]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Participant decides from the coordinator's broadcast.
DecideFromCoordinator(p) ==
    /\ alive[p]
    /\ decision[p] = undecided
    /\ coordBroadcast[p] # notsent
    /\ decision' = [decision EXCEPT ![p] = coordBroadcast[p]]
    /\ UNCHANGED <<vote, alive, faulty, sent, coordSent,
                   recvd, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* A participant crashes silently.
DieParticipant(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ faulty' = [faulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, sent, coordSent,
                   recvd, coordBroadcast, coordDecision, coordAlive, coordFaulty>>

\* Progress for participants/coordinator is weakly fair (always possible);
\* death is not, so a crash can always stall the protocol.
Next ==
    \/ \E p \in participants:
         \/ SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p)
         \/ Broadcast(p) \/ SendVote(p) \/ AbortNo(p) \/ AbortReqTimeout(p)
         \/ DecideFromCoordinator(p) \/ DieParticipant(p)
    \/ MakeDecision \/ DieCoordinator

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants:
         /\ WF_vars(SendVoteRequest(p)) /\ WF_vars(ReceiveVote(p))
         /\ WF_vars(DetectFault(p)) /\ WF_vars(Broadcast(p))
         /\ WF_vars(SendVote(p)) /\ WF_vars(AbortNo(p))
         /\ WF_vars(AbortReqTimeout(p)) /\ WF_vars(DecideFromCoordinator(p))

(* SAFETY: no two participants ever decide differently.                    *)
AC1 == \A p1, p2 \in participants:
           ~(decision[p1] = commit /\ decision[p2] = abort)

(* SAFETY: commit can only happen if every vote was yes.                  *)
AC2 == \A p \in participants: decision[p] = commit => \A q \in participants: vote[q] = yes

(* SAFETY: abort only if a no vote exists or some actor is faulty.       *)
AC3 == \A p \in participants: decision[p] = abort =>
          (\E q \in participants: vote[q] = no) \/ (\E q \in participants: faulty[q])
             \/ coordFaulty

(* SAFETY: a decided participant never flips its decision.                *)
AC4 == \A p \in participants:
          /\ (decision[p] = commit => [decision EXCEPT ![p] = commit] = decision)
          /\ (decision[p] = abort => [decision EXCEPT ![p] = abort] = decision)

(* LIVENESS: either everyone decides, or some actor is faulty.           *)
AC3Live == <>(\A p \in participants: decision[p] # undecided) \/ (\E p \in participants: faulty[p]) \/ coordFaulty

Properties == AC3Live

\* The simple broadcast variant does NOT guarantee AC5 (non-blocking
\* termination): a coordinator crash mid-broadcast can leave participants
\* undecided forever.  The model still tracks the weaker AC3Live liveness.
====