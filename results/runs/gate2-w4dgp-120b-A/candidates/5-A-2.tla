---- MODULE ACP_SB ----
EXTENDS Naturals

(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB) by Babaoglu and    *)
(* Toueg.  One coordinator collects votes from participants; it then decides  *)
(* commit or abort, and broadcasts that decision.  The simple broadcast is      *)
(* sequential, so a coordinator failure during broadcast can leave a           *)
(* participant undecided -- this is the blocking failure case.  The spec       *)
(* tracks, per participant, the vote taken, the final decision, whether the    *)
(* participant is faulty, and whether it sent its vote; and, for the            *)
(* coordinator, the requests sent, the votes received, the broadcasts sent,    *)
(* the decision, and whether it is faulty.  It implements the full action set  *)
(* described in the problem, plus the four safety properties AC1-AC4 and the   *)
(* liveness component of AC3 (termination or fault).                           *)

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision,
          participantFaulty, voteSent,
          requestSent, receivedVote, broadcastSent, coordinatorDecision,
          coordinatorAlive, coordinatorFaulty

vars == <<participantVote, participantAlive, participantDecision,
          participantFaulty, voteSent,
          requestSent, receivedVote, broadcastSent, coordinatorDecision,
          coordinatorAlive, coordinatorFaulty>>

TypeInv ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ requestSent \in [participants -> BOOLEAN]
    /\ receivedVote \in [participants -> {yes, no, waiting}]
    /\ broadcastSent \in [participants -> {notsent, commit, abort}]
    /\ coordinatorDecision \in {undecided, commit, abort}
    /\ coordinatorAlive \in BOOLEAN
    /\ coordinatorFaulty \in BOOLEAN

Init ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ requestSent = [p \in participants |-> FALSE]
    /\ receivedVote = [p \in participants |-> waiting]
    /\ broadcastSent = [p \in participants |-> notsent]
    /\ coordinatorDecision = undecided
    /\ coordinatorAlive = TRUE
    /\ coordinatorFaulty = FALSE

\* A batch of vote requests (the coordinator sends them one at a time).
SendVoteRequest(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ ~requestSent[p]
    /\ requestSent' = [requestSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   receivedVote, broadcastSent, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

\* The coordinator receives a vote from a participant that has sent it.
ReceiveVote(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ voteSent[p]
    /\ receivedVote' = [receivedVote EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   requestSent, broadcastSent, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

\* The coordinator detects a participant that went silent/died before voting,
\* which forces an abort (the blocking failure case of this protocol).
DetectParticipantFault(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ requestSent[p]
    /\ receivedVote[p] = waiting
    /\ ~participantAlive[p]
    /\ coordinatorDecision' = abort
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   requestSent, receivedVote, broadcastSent,
                   coordinatorAlive, coordinatorFaulty>>

MakeDecision ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ \A p \in participants : requestSent[p]
    /\ \A p \in participants : receivedVote[p] # waiting
    /\ coordinatorDecision' = IF \A p \in participants : receivedVote[p] = yes
                              THEN commit ELSE abort
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   requestSent, receivedVote, broadcastSent,
                   coordinatorAlive, coordinatorFaulty>>

\* Simple broadcast: the coordinator sends its decision to one participant
\* at a time, so a crash here leaves trailing participants undecided.
BroadcastDecision(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision # undecided
    /\ broadcastSent[p] = notsent
    /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordinatorDecision]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   requestSent, receivedVote, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

DieCoordinator ==
    /\ coordinatorAlive
    /\ coordinatorAlive' = FALSE
    /\ coordinatorFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, voteSent,
                   requestSent, receivedVote, broadcastSent, coordinatorDecision>>

SendVote(p) ==
    /\ participantAlive[p]
    /\ requestSent[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty,
                   requestSent, receivedVote, broadcastSent,
                   coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

\* A participant may unilaterally abort if it voted no.
DecideAbort(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ voteSent[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   voteSent, requestSent, receivedVote,
                   broadcastSent, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

\* A participant times out a missing coordinator request by aborting if the
\* coordinator has died without ever requesting it.
AbortOnCoordinatorTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordinatorAlive
    /\ ~requestSent[p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   voteSent, requestSent, receivedVote, broadcastSent,
                   coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

DecideOnBroadcast(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ broadcastSent[p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = broadcastSent[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   voteSent, requestSent, receivedVote,
                   broadcastSent, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

DieParticipant(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantDecision,
                   voteSent, requestSent, receivedVote,
                   broadcastSent, coordinatorDecision,
                   coordinatorAlive, coordinatorFaulty>>

Next ==
    \/ \E p \in participants :
        \/ SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p)
        \/ BroadcastDecision(p) \/ SendVote(p) \/ DecideAbort(p)
        \/ AbortOnCoordinatorTimeout(p) \/ DecideOnBroadcast(p)
        \/ DieParticipant(p)
    \/ MakeDecision \/ DieCoordinator

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(SendVoteRequest(SUBSET participants))
    /\ WF_vars(ReceiveVote(SUBSET participants))
    /\ WF_vars(SendVote(SUBSET participants))
    /\ WF_vars(DecideAbort(SUBSET participants))
    /\ WF_vars(DecideOnBroadcast(SUBSET participants))
    /\ WF_vars(AbortOnCoordinatorTimeout(SUBSET participants))

\* AC1: no two participants decide differently (consistency / agreement)
AC1 == \A p, q \in participants :
           ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

\* AC2: a commit is only possible if every participant voted yes (validity)
AC2 == \A p \in participants : participantDecision[p] = commit => participantVote[p] = yes

\* AC3: an abort is backed by a no vote or a detected fault on at least one node
AC3 == \A p \in participants : participantDecision[p] = abort
           => (\E q \in participants : participantVote[q] = no \/ participantFaulty[q] \/ coordinatorFaulty)

\* AC4: each participant decides at most once -- the state is locked once decided
AC4 == \A p \in participants :
           /\ (participantDecision[p] = commit => participantDecision' = [participantDecision EXCEPT ![p] = commit])
           /\ (participantDecision[p] = abort => participantDecision' = [participantDecision EXCEPT ![p] = abort])

\* AC3 termination component: every non-faulty participant eventually decides,
\* or at least one node (coordinator or participant) is detected faulty.
AC3Live == <>(\A p \in participants : participantDecision[p] # undecided \/ participantFaulty[p] \/ coordinatorFaulty)

====