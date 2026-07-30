---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecide \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordReq \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecide \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [pt \in participants |-> TRUE]
    /\ pDecide = [pt \in participants |-> undecided]
    /\ pFaulty = [pt \in participants |-> FALSE]
    /\ pSent = [pt \in participants |-> FALSE]
    /\ coordReq = [pt \in participants |-> FALSE]
    /\ coordRecv = [pt \in participants |-> waiting]
    /\ coordSent = [pt \in participants |-> notsent]
    /\ coordDecide = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

RequestVote(pt) ==
    /\ coordAlive
    /\ ~coordReq[pt]
    /\ coordReq' = [coordReq EXCEPT ![pt] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordRecv, coordSent, coordDecide, coordFaulty>>

ReceiveVote(pt) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ coordReq[pt]
    /\ coordRecv[pt] = waiting
    /\ pSent[pt]
    /\ coordRecv' = [coordRecv EXCEPT ![pt] = pVote[pt]]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordSent, coordDecide, coordAlive, coordFaulty>>

DetectFault(pt) ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ coordReq[pt]
    /\ coordRecv[pt] = waiting
    /\ ~pAlive[pt]
    /\ coordDecide' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

Decide ==
    /\ coordAlive
    /\ coordDecide = undecided
    /\ \A pt \in participants : coordRecv[pt] # waiting
    /\ coordDecide' = IF \A pt \in participants : coordRecv[pt] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(pt) ==
    /\ coordAlive
    /\ coordDecide # undecided
    /\ coordSent[pt] = notsent
    /\ coordSent' = [coordSent EXCEPT ![pt] = coordDecide]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordDecide, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide>>

SendVote(pt) ==
    /\ pAlive[pt]
    /\ coordReq[pt]
    /\ ~pSent[pt]
    /\ pSent' = [pSent EXCEPT ![pt] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecide, pFaulty, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

AbortVote(pt) ==
    /\ pAlive[pt]
    /\ pDecide[pt] = undecided
    /\ pSent[pt]
    /\ pVote[pt] = no
    /\ pDecide' = [pDecide EXCEPT ![pt] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

AbortOnNoRequest(pt) ==
    /\ pAlive[pt]
    /\ pDecide[pt] = undecided
    /\ coordAlive = FALSE
    /\ pSent[pt] = FALSE
    /\ pDecide' = [pDecide EXCEPT ![pt] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

DecideFromCoord(pt) ==
    /\ pAlive[pt]
    /\ pDecide[pt] = undecided
    /\ coordSent[pt] # notsent
    /\ pDecide' = [pDecide EXCEPT ![pt] = coordSent[pt]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

ParticipantDie(pt) ==
    /\ pAlive[pt]
    /\ pAlive' = [pAlive EXCEPT ![pt] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![pt] = TRUE]
    /\ UNCHANGED <<pVote, pDecide, pSent, coordReq, coordRecv, coordSent, coordDecide, coordAlive, coordFaulty>>

Next ==
    \/ \E pt \in participants : RequestVote(pt)
    \/ \E pt \in participants : ReceiveVote(pt)
    \/ \E pt \in participants : DetectFault(pt)
    \/ Decide
    \/ \E pt \in participants : BroadcastDecision(pt)
    \/ CoordDie
    \/ \E pt \in participants : SendVote(pt)
    \/ \E pt \in participants : AbortVote(pt)
    \/ \E pt \in participants : AbortOnNoRequest(pt)
    \/ \E pt \in participants : DecideFromCoord(pt)
    \/ \E pt \in participants : ParticipantDie(pt)

Spec == Init /\ [][Next]_vars /\ WF_vars(SendVote(choice)) /\ WF_vars(Decide) /\ WF_vars(BroadcastDecision(choice)) /\ WF_vars(AbortVote(choice))

Agreement ==
    \A x, y \in participants :
        (pDecide[x] = commit /\ pDecide[y] = abort) => FALSE

CommitValidity == \A pt \in participants : pDecide[pt] = commit => \A q \in participants : pVote[q] = yes

AbortValidity == \A pt \in participants : pDecide[pt] = abort => (NO \in {pVote[q] : q \in participants} \/ \E q \in participants : pFaulty[q] \/ coordFaulty)

Irreversible ==
    /\ \A pt \in participants : (pDecide[pt] = commit) ~> (pDecide[pt] = commit)
    /\ \A pt \in participants : (pDecide[pt] = abort) ~> (pDecide[pt] = abort)

SomeDecision ==
    \E pt \in participants : pDecide[pt] # undecided

Resolve ==
    \/ SomeDecision
    \/ \E pt \in participants : pFaulty[pt]
    \/ coordFaulty

DecideEventually == SomeDecision \/ Resolve

====