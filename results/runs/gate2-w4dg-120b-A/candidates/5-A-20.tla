---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Decision mapping for participants: what the coordinator broadcast to each.
VARIABLES pVote, pAlive, pDecide, pFaulty, pSent,
         coordReqd, coordBallot, coordBroadcasted,
         coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, pSent,
          coordReqd, coordBallot, coordBroadcasted,
          coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordReqd \in [participants -> BOOLEAN]
    /\ coordBallot \in [participants -> {yes, no, waiting}]
    /\ coordBroadcasted \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [pp \in participants |-> TRUE]
    /\ pDecide = [pp \in participants |-> undecided]
    /\ pFaulty = [pp \in participants |-> FALSE]
    /\ pSent = [pp \in participants |-> FALSE]
    /\ coordReqd = [pp \in participants |-> FALSE]
    /\ coordBallot = [pp \in participants |-> waiting]
    /\ coordBroadcasted = [pp \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* The coordinator sends a vote request to a participant (simple broadcast).
SendVoteReq(pp) ==
    /\ coordAlive
    /\ ~coordReqd[pp]
    /\ coordReqd' = [coordReqd EXCEPT ![pp] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

\* The coordinator receives a participant's vote (which must have been sent).
ReceiveVote(pp) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReqd[pp]
    /\ coordBallot[pp] = waiting
    /\ pSent[pp]
    /\ coordBallot' = [coordBallot EXCEPT ![pp] = pVote[pp]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordReqd, coordBroadcasted, coordDecision,
                  coordAlive, coordFaulty>>

\* The coordinator detects a participant fault (dies without sending its vote).
DetectParticipantFault(pp) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReqd[pp]
    /\ coordBallot[pp] = waiting
    /\ ~pAlive[pp]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordAlive, coordFaulty>>

\* The coordinator makes its decision once all votes are collected.
MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A pp \in participants : coordBallot[pp] # waiting
    /\ coordDecision' = IF \A pp \in participants : coordBallot[pp] = yes
                         THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordAlive, coordFaulty>>

\* The coordinator broadcasts its decision via simple broadcast.
BroadcastDecision(pp) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordBroadcasted[pp] = notsent
    /\ coordBroadcasted' = [coordBroadcasted EXCEPT ![pp] = coordDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordReqd, coordBallot, coordDecision,
                  coordAlive, coordFaulty>>

DieCoordinator ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision>>

\* A participant sends its vote to the coordinator.
SendVote(pp) ==
    /\ pAlive[pp]
    /\ coordReqd[pp]
    /\ ~pSent[pp]
    /\ pSent' = [pSent EXCEPT ![pp] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

\* A participant aborts unilaterally on having voted no.
AbortOnVote(pp) ==
    /\ pAlive[pp]
    /\ pDecide[pp] = undecided
    /\ pSent[pp]
    /\ pVote[pp] = no
    /\ pDecide' = [pDecide EXCEPT ![pp] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

\* A participant aborts on timeout for the coordinator's vote request.
AbortOnTimeout(pp) ==
    /\ pAlive[pp]
    /\ pDecide[pp] = undecided
    /\ ~coordAlive
    /\ ~coordReqd[pp]
    /\ pDecide' = [pDecide EXCEPT ![pp] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

\* A participant decides the same as what the coordinator broadcast.
DecideOnBroadcast(pp) ==
    /\ pAlive[pp]
    /\ pDecide[pp] = undecided
    /\ coordDecision # undecided
    /\ coordBroadcasted[pp] # notsent
    /\ pDecide' = [pDecide EXCEPT ![pp] = coordBroadcasted[pp]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

DieParticipant(pp) ==
    /\ pAlive[pp]
    /\ pAlive' = [pAlive EXCEPT ![pp] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![pp] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, pSent,
                  coordReqd, coordBallot, coordBroadcasted,
                  coordDecision, coordAlive, coordFaulty>>

CoordinatorProgress ==
    \/ \E pp \in participants : SendVoteReq(pp)
    \/ \E pp \in participants : ReceiveVote(pp)
    \/ \E pp \in participants : DetectParticipantFault(pp)
    \/ MakeDecision
    \/ \E pp \in participants : BroadcastDecision(pp)
    \/ DieCoordinator

ParticipantProgress ==
    \/ \E pp \in participants : SendVote(pp)
    \/ \E pp \in participants : AbortOnVote(pp)
    \/ \E pp \in participants : AbortOnTimeout(pp)
    \/ \E pp \in participants : DecideOnBroadcast(pp)

Next ==
    \/ CoordinatorProgress
    \/ ParticipantProgress
    \/ \E pp \in participants : DieParticipant(pp)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CoordinatorProgress)
        /\ WF_vars(ParticipantProgress)

\* Safety: no two participants decide differently.
Agreement ==
    \A p \in participants : \A q \in participants :
        (pDecide[p] = commit /\ pDecide[q] = abort) ~> FALSE

\* Safety: a commit requires all yes votes.
CommitValidity ==
    (\E p \in participants : pDecide[p] = commit)
        ~> (\A q \in participants : pVote[q] = yes)

\* Safety: an abort requires a no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
    (\E p \in participants : pDecide[p] = abort)
        ~> (\E q \in participants : pVote[q] = no \/ pFaulty[q])
            \/ coordFaulty

\* Safety: each participant decides at most once (irreversibly).
Irreversibility ==
    \A p \in participants :
        /\ (pDecide[p] = commit) ~> (pDecide[p] = commit)
        /\ (pDecide[p] = abort) ~> (pDecide[p] = abort)

\* Liveness: either everyone decides, or some process is faulty.
EventualDecision ==
    <>( \A p \in participants : pDecide[p] # undecided
         \/ (\E q \in participants : pFaulty[q])
         \/ coordFaulty)

====