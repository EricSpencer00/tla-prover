---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

TypeOK ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ voted \in [participants -> BOOLEAN]
    /\ posted \in [participants -> BOOLEAN]
    /\ cReqs \in [participants -> BOOLEAN]
    /\ cRecv \in [participants -> {yes, no, waiting}]
    /\ cSent \in [participants -> {commit, abort, notsent}]
    /\ cDecide \in {undecided, commit, abort}
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN

Init ==
    /\ \E v \in [participants -> {yes, no}] : pVote = v
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecide = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ voted = [p \in participants |-> FALSE]
    /\ posted = [p \in participants |-> FALSE]
    /\ cReqs = [p \in participants |-> FALSE]
    /\ cRecv = [p \in participants |-> waiting]
    /\ cSent = [p \in participants |-> notsent]
    /\ cDecide = undecided
    /\ cAlive = TRUE
    /\ cFaulty = FALSE

SubmitVote(p) == pAlive[p] /\ voted[p]

RequestVote(p ==
    /\ cAlive
    /\ ~cReqs[p]
    /\ cReqs' = [cReqs EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cRecv, cSent, cDecide, cAlive, cFaulty>>

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A q \in participants : cReqs[q]
    /\ cRecv[p] = waiting
    /\ SubmitVote(p)
    /\ cRecv' = [cRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cSent, cDecide, cAlive, cFaulty>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A q \in participants : cReqs[q]
    /\ cRecv[p] = waiting
    /\ ~SubmitVote(p)
    /\ ~pAlive[p]
    /\ cDecide' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cSent, cAlive, cFaulty>>

MakeDecision ==
    /\ cAlive
    /\ cDecide = undecided
    /\ \A p \in participants : cRecv[p] # waiting
    /\ cDecide' = IF \A p \in participants : cRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cSent, cAlive, cFaulty>>

Broadcast(p) ==
    /\ cAlive
    /\ cDecide # undecided
    /\ cSent[p] = notsent
    /\ cSent' = [cSent EXCEPT ![p] = cDecide]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cDecide, cAlive, cFaulty>>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide>>

SendVote(p) ==
    /\ pAlive[p]
    /\ cReqs[p]
    /\ ~voted[p]
    /\ voted' = [voted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ voted[p]
    /\ pVote[p] = no
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ ~cAlive
    /\ ~cReqs[p]
    /\ pDecide' = [pDecide EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

DecideFromCoord(p) ==
    /\ pAlive[p]
    /\ pDecide[p] = undecided
    /\ cSent[p] # notsent
    /\ pDecide' = [pDecide EXCEPT ![p] = cSent[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, voted, posted, cReqs, cRecv, cSent, cDecide, cAlive, cFaulty>>

CoordinatorProgress == \E p \in participants : RequestVote(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p)

ParticipantProgress == \E p \in participants : SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromCoord(p)

Next ==
    \/ CoordinatorProgress
    \/ ParticipantProgress
    \/ MakeDecision
    \/ DieCoordinator
    \/ \E p \in participants : DieParticipant(p)

Spec == Init /\ [][Next]_vars /\ SF_Vars(ParticipantProgress) /\ WF_Vars(CoordinatorProgress)

Agreement ==
    \A p, q \in participants :
        ~(pDecide[p] = commit /\ pDecide[q] = abort)

CommitValidity ==
    (\E p \in participants : pDecide[p] = commit) => (\A p \in participants : pVote[p] = yes)

AbortValidity ==
    (\E p \in participants : pDecide[p] = abort) => (\E p \in participants : pVote[p] = no) \/ (\E p \in participants : pFaulty[p]) \/ cFaulty

Irreversibility ==
    \A p \in participants :
        /\ (pDecide[p] = commit => (pDecide' = [pDecide EXCEPT ![p] = commit] \/ UNCHANGED vars))
        /\ (pDecide[p] = abort => (pDecide' = [pDecide EXCEPT ![p] = abort] \/ UNCHANGED vars))

Liveness == <>(\A p \in participants : pDecide[p] # undecided \/ (\E p \in participants : pFaulty[p]) \/ cFaulty)

TypeInv == TypeOK

====