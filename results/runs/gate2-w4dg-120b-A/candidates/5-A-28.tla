---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent, cVoteRecv,
          cDecisionSent, cDecision, cAlive, cFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent, cVoteRecv,
          cDecisionSent, cDecision, cAlive, cFaulty>>

Bump(f, x) == [f EXCEPT ![x] = TRUE]
SetDec(v) == IF v = commit THEN commit ELSE abort

TypeOK ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ cReqSent \in [participants -> BOOLEAN]
    /\ cVoteRecv \in [participants -> {yes, no, waiting}]
    /\ cDecisionSent \in [participants -> {commit, abort, notsent}]
    /\ cDecision \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [x \in participants |-> TRUE]
    /\ pDecision = [x \in participants |-> undecided]
    /\ pFaulty = [x \in participants |-> FALSE]
    /\ pSentVote = [x \in participants |-> FALSE]
    /\ cReqSent = [x \in participants |-> FALSE]
    /\ cVoteRecv = [x \in participants |-> waiting]
    /\ cDecisionSent = [x \in participants |-> notsent]
    /\ cDecision = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

SendReq(x) ==
    /\ cAlive
    /\ ~cReqSent[x]
    /\ cReqSent' = [cReqSent EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

RecvVote(x) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[x]
    /\ cVoteRecv[x] = waiting
    /\ pSentVote[x]
    /\ cVoteRecv' = [cVoteRecv EXCEPT ![x] = pVote[x]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

DetectFault(x) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cReqSent[x]
    /\ cVoteRecv[x] = waiting
    /\ ~pAlive[x]
    /\ cDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent,
                    cVoteRecv, cDecisionSent, cDecision, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A x \in participants : cVoteRecv[x] # waiting
    /\ cDecision' = SetDec([x \in participants |-> cVoteRecv[x]])[yes]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent,
                    cVoteRecv, cDecisionSent, cDecision, cAlive, cFaulty>>

Broadcast(x) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cDecisionSent[x] = notsent
    /\ cDecisionSent' = [cDecisionSent EXCEPT ![x] = cDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent,
                    cVoteRecv, cDecision, cAlive, cFaulty>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote, cReqSent,
                    cVoteRecv, cDecisionSent, cDecision, cAlive, cFaulty>>

SendMyVote(x) ==
    /\ pAlive[x]
    /\ cReqSent[x]
    /\ ~pSentVote[x]
    /\ pSentVote' = [pSentVote EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, cReqSent, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

PartAbortVote(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ pSentVote[x]
    /\ pVote[x] = no
    /\ pDecision' = [pDecision EXCEPT ![x] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, cReqSent, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

PartAbortTimeout(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ ~cAlive
    /\ ~cReqSent[x]
    /\ pDecision' = [pDecision EXCEPT ![x] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, cReqSent, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

DecideFromCoord(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ cDecisionSent[x] # notsent
    /\ pDecision' = [pDecision EXCEPT ![x] = cDecisionSent[x]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote, cReqSent, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

PartDie(x) ==
    /\ pAlive[x]
    /\ pAlive' = [pAlive EXCEPT ![x] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSentVote, cReqSent, cVoteRecv,
                    cDecisionSent, cDecision, cAlive, cFaulty>>

Next ==
    \/ \E x \in participants : SendReq(x)
    \/ \E x \in participants : RecvVote(x)
    \/ \E x \in participants : DetectFault(x)
    \/ MakeDecision
    \/ \E x \in participants : Broadcast(x)
    \/ CoordDie
    \/ \E x \in participants : SendMyVote(x)
    \/ \E x \in participants : PartAbortVote(x)
    \/ \E x \in participants : PartAbortTimeout(x)
    \/ \E x \in participants : DecideFromCoord(x)
    \/ \E x \in participants : PartDie(x)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E x \in participants : SendMyVote(x))
        /\ WF_vars(\E x \in participants : PartAbortVote(x))
        /\ WF_vars(\E x \in participants : PartAbortTimeout(x))
        /\ WF_vars(\E x \in participants : DecideFromCoord(x))
        /\ WF_vars(\E x \in participants : Broadcast(x))
        /\ WF_vars(\E x \in participants : RecvVote(x))

\* No two participants ever decide differently.
Agreement ==
    \A x, y \in participants : ~(pDecision[x] = commit /\ pDecision[y] = abort)

\* Commit is unanimous: any committed participant was voted yes by everyone.
ValidCommit ==
    \A x \in participants : pDecision[x] = commit => (\A y \in participants : pVote[y] = yes)

\* Abort happens only on a no vote or a failure: at least one no vote or a faulty
\* participant or a faulty coordinator must explain an abort.
ValidAbort ==
    \A x \in participants : pDecision[x] = abort => \/ \E y \in participants : pVote[y] = no
                                                  \/ \E y \in participants : pFaulty[y]
                                                  \/ cFaulty

\* Decisions are irreversible: a commit stays a commit, an abort stays an abort.
Irreversible ==
    \A x \in participants : (pDecision[x] = commit => pDecision' [x] = commit)
                     /\  (pDecision[x] = abort => pDecision' [x] = abort)

\* The liveness property reflects the fact that the simple broadcast variant can
\* block: either everyone decides, or some participant is faulty, or the
\* coordinator is faulty -- the system never sits undecided forever with nobody
\* possibly left to decide.
Ac3Liveness == <>(\A x \in participants : pDecision[x] # undecided \/ pFaulty[x] \/ cFaulty)

====