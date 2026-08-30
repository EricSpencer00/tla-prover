---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), a blocking variant
\* of the two-phase commit style protocol. A coordinator collects votes from
\* participants and then broadcasts its commit/abort decision; if the
\* coordinator crashes mid-broadcast, undecided participants are left hanging,
\* which is exactly what breaks the non-blocking termination property.

VARIABLES pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty

vars == <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecided \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ rReq \in [participants -> {waiting, sent}]
    /\ rRecv \in [participants -> {waiting, yes, no}]
    /\ rBroadcast \in [participants -> {notsent, commit, abort}]
    /\ rDecided \in {undecided, commit, abort}
    /\ rAlive \in BOOLEAN
    /\ rFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecided = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pSent = [p \in participants |-> FALSE]
    /\ rReq = [p \in participants |-> waiting]
    /\ rRecv = [p \in participants |-> waiting]
    /\ rBroadcast = [p \in participants |-> notsent]
    /\ rDecided = undecided
    /\ rAlive = TRUE
    /\ rFaulty = FALSE

\* Coordinator actions:

ReqVote(p) ==
    /\ rAlive
    /\ rReq[p] = waiting
    /\ rReq' = [rReq EXCEPT ![p] = sent]
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

RecvVote(p) ==
    /\ rAlive
    /\ rDecided = undecided
    /\ rReq[p] = sent
    /\ rRecv[p] = waiting
    /\ pSent[p]
    /\ rRecv' = [rRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rBroadcast, rDecided, rAlive, rFaulty>>

DetectFault(p) ==
    /\ rAlive
    /\ rDecided = undecided
    /\ rReq[p] = sent
    /\ rRecv[p] = waiting
    /\ ~pAlive[p]
    /\ rDecided' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rBroadcast, rAlive, rFaulty>>

Decide ==
    /\ rAlive
    /\ rDecided = undecided
    /\ \A p \in participants : rRecv[p] # waiting
    /\ rDecided' = IF \A p \in participants : rRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rBroadcast, rAlive, rFaulty>>

Broadcast(p) ==
    /\ rAlive
    /\ rDecided # undecided
    /\ rBroadcast[p] = notsent
    /\ rBroadcast' = [rBroadcast EXCEPT ![p] = rDecided]
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rDecided, rAlive, rFaulty>>

RDie ==
    /\ rAlive
    /\ rAlive' = FALSE
    /\ rFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided>>

\* Participant actions:

SendVote(p) ==
    /\ pAlive[p]
    /\ rReq[p] = sent
    /\ ~pSent[p]
    /\ pSent' = [pSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecided, pFaulty, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

AbortVote(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ pSent[p]
    /\ pVote[p] = no
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

AbortReqTimeout(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ rReq[p] = waiting
    /\ ~rAlive
    /\ pDecided' = [pDecided EXCEPT ![p] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

DecideFromCoord(p) ==
    /\ pAlive[p]
    /\ pDecided[p] = undecided
    /\ rBroadcast[p] # notsent
    /\ pDecided' = [pDecided EXCEPT ![p] = rBroadcast[p]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

PDie(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<pVote, pDecided, pSent, rReq, rRecv, rBroadcast, rDecided, rAlive, rFaulty>>

\* The coordinator's decision is never a silent no-op: every vote or timeout
\* that forces an abort is written into rDecided immediately, so the two
\* participants cannot both end up committing, even if the coordinator dies
\* right after making its (now-consistent) decision but before broadcasting it.

Next ==
    \/ \E p \in participants : ReqVote(p)
    \/ \E p \in participants : RecvVote(p)
    \/ \E p \in participants : DetectFault(p)
    \/ Decide
    \/ \E p \in participants : Broadcast(p)
    \/ RDie
    \/ \E p \in participants : SendVote(p)
    \/ \E p \in participants : AbortVote(p)
    \/ \E p \in participants : AbortReqTimeout(p)
    \/ \E p \in participants : DecideFromCoord(p)
    \/ \E p \in participants : PDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in participants : WF_vars(SendVote(p))
    /\ \A p \in participants : WF_vars(AbortVote(p))
    /\ \A p \in participants : WF_vars(DecideFromCoord(p))
    /\ \A p \in participants : WF_vars(AbortReqTimeout(p))
    /\ \A p \in participants : SF_vars(ReqVote(p))
    /\ \A p \in participants : SF_vars(RecvVote(p))
    /\ \A p \in participants : SF_vars(DetectFault(p))
    /\ WF_vars(Decide)

\* Safety: commitment is coherent and irreversible across participants.

Agreement ==
    \A p1 \in participants, p2 \in participants :
        ~ (pDecided[p1] = commit /\ pDecided[p2] = abort)

CommitValidity ==
    \A p \in participants : pDecided[p] = commit => (\A q \in participants : pVote[q] = yes)

AbortValidity ==
    \A p \in participants :
        pDecided[p] = abort =>
            \/ \E q \in participants : pVote[q] = no
            \/ \E q \in participants : pFaulty[q]
            \/ rFaulty

Irreversibility ==
    \A p \in participants :
        /\ (pDecided[p] = commit => (pDecided[p] = commit) [][F]_<<pDecided>>
        /\ (pDecided[p] = abort => (pDecided[p] = abort) [][F]_<<pDecided>>

\* Liveness: the two-phase protocol either reaches a decision or crashes; it
\* does NOT guarantee every non-faulty participant eventually decides under
\* simple broadcast, so the stronger AC5 property is intentionally omitted.

DecideOrCrash ==
    <>(\A p \in participants : pDecided[p] # undecided \/ pFaulty[p]) \/ rFaulty

====