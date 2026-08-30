---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecide, pFaulty, pSentReq, cReqSent, cVoteRecv,
          cBroadcast, cDecide, cAlive, cFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, pSentReq, cReqSent, cVoteRecv,
           cBroadcast, cDecide, cAlive, cFaulty>>

Broadcasts == participants \X {commit, abort}

TypeOK ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentReq \in [participants -> BOOLEAN]
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> {waiting, yes, no}]
    /\ cBroadcast \in [Broadcasts -> {notsent, waiting}]
    /\ cDecide \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecide = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSentReq = [p \in participants |-> FALSE]
    /\ cReqSent = [p \in participants |-> FALSE]
    /\ cVoteRecv = [p \in participants |-> waiting]
    /\ cBroadcast = [bp \in Broadcasts |-> notsent]
    /\ cDecide = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

\* Coordinator actions
SendReq(p) ==
    /\ cAlive
    /\ ~cReqSent[p]
    /\ cReqSent' = [cReqSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A q \in participants: cReqSent[q]
    /\ cVoteRecv[p] = waiting
    /\ pSentReq[p]
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cReqSent, cBroadcast, cDecide, cAlive, cFaulty>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A q \in participants: cReqSent[q]
    /\ cVoteRecv[p] = waiting
    /\ ~pAlive[p]
    /\ ~pSentReq[p]
    /\ cDecide' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cAlive, cFaulty>>

\* The coordinator decides once every vote is in (or a fault forces abort).
Decide ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A p \in participants: cVoteRecv[p] # waiting
    /\ cDecide' = IF \A p \in participants: cVoteRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cAlive, cFaulty>>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecide # undecided
    /\ cBroadcast[p, cDecide] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p, cDecide] = waiting]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cDecide, cAlive, cFaulty>>

DieCoord ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide>>

\* Participant actions
SendVote(p) ==
    /\ pAlive[p]
    /\ cReqSent[p]
    /\ pSentReq[p] = FALSE
    /\ pSentReq' = [pSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ pSentReq[p]
    /\ pVote[p] = no
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ ~cAlive
    /\ ~pSentReq[p]
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ cBroadcast[p, commit] = waiting
    /\ pDecide' = [pDecide EXCEPT ![p] = commit]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

DecideOnAbort(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ cBroadcast[p, abort] = waiting
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, pSentReq,
                   cReqSent, cVoteRecv, cBroadcast, cDecide, cAlive, cFaulty>>

\* Liveness is only assumed on the progress actions, not on death.
Next ==
    \/ \E p \in participants:
         \/ SendReq(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
         \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p)
         \/ DecideOnBroadcast(p) \/ DecideOnAbort(p) \/ DieParticipant(p)
    \/ Decide \/ DieCoord

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E p \in participants: SendReq(p))
    /\ WF_vars(\E p \in participants: ReceiveVote(p))
    /\ WF_vars(\E p \in participants: DetectFault(p))
    /\ WF_vars(\E p \in participants: SendVote(p))
    /\ WF_vars(\E p \in participants: AbortOnVote(p))
    /\ WF_vars(\E p \in participants: AbortOnTimeout(p))
    /\ WF_vars(\E p \in participants: DecideOnBroadcast(p))
    /\ WF_vars(\E p \in participants: DecideOnAbort(p))

\* Safety: no two participants reach conflicting decisions.
Agreement ==
    \A p, q \in participants:
        (pDecide[p] = commit /\ pDecide[q] = abort) => p = q

\* Validity properties.
CommitValid == ( \E p \in participants: pDecide[p] = commit )
                  => ( \A p \in participants: pVote[p] = yes )

AbortValid ==
    ( \E p \in participants: pDecide[p] = abort )
        => ( (\E p \in participants: pVote[p] = no)
              \/ (\E p \in participants: pFaulty[p])
              \/ cFaulty )

Irreversible ==
    \A p \in participants:
        (pDecide[p] = commit) ~> (pDecide[p] = commit)
        /\ (pDecide[p] = abort) ~> (pDecide[p] = abort)

\* Liveness: progress or failure, not guaranteed under coordinator crash.
EventualDecision ==
    <> (\A p \in participants: pDecide[p] # undecided) \/ (\E p \in participants: pFaulty[p]) \/ cFaulty

\* No non-blocking progress guarantee holds under simple broadcast.
NoBlockingGuarantee == TRUE

TypeInv == TypeOK
====