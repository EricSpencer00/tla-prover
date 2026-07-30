---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pAlive, pDecision, pFaulty, pVote, pRequested, pRecvd,
         cAlive, cDecision, cFaulty, cSent

vars == <<pAlive, pDecision, pFaulty, pVote, pRequested, pRecvd,
          cAlive, cDecision, cFaulty, cSent>>

TypeInv ==
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pRequested \in [participants -> BOOLEAN]
    /\ pRecvd \in [participants -> {yes, no, waiting}]
    /\ cAlive \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cFaulty \in BOOLEAN
    /\ cSent \in [participants -> {notsent, commit, abort}]

Init ==
    /\ pAlive = [x \in participants |-> TRUE]
    /\ pDecision = [x \in participants |-> undecided]
    /\ pFaulty = [x \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes, no}]
    /\ pRequested = [x \in participants |-> FALSE]
    /\ pRecvd = [x \in participants |-> waiting]
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cFaulty = FALSE
    /\ cSent = [x \in participants |-> notsent]

\* Simple broadcast: the coordinator sends the decision to each participant one
\* at a time, so a crash while broadcasting can strand a participant undecided.
SendReq(x) ==
    /\ cAlive
    /\ ~pRequested[x]
    /\ pRequested' = [pRequested EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRecvd, cAlive, cDecision, cFaulty, cSent>>

RecvVote(x) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ pRequested[x]
    /\ pRecvd[x] = waiting
    /\ pAlive[x]
    /\ pRecvd' = [pRecvd EXCEPT ![x] = pVote[x]]
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, cAlive, cDecision, cFaulty, cSent>>

DetectFault(x) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ pRequested[x]
    /\ pRecvd[x] = waiting
    /\ ~pAlive[x]
    /\ cDecision' = abort
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cSent>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A x \in participants : pRecvd[x] # waiting
    /\ cDecision' = IF \A x \in participants : pRecvd[x] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cFaulty, cSent>>

BroadcastDecision(x) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cSent[x] = notsent
    /\ cSent' = [cSent EXCEPT ![x] = cDecision]
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cDecision, cFaulty>>

CoordDie ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, pRecvd, cDecision, cSent>>

\* A participant that voted no unilaterally aborts, which is how the protocol
\* guarantees that no participant ever commits on a no vote.
AbortOnNoVote(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ pRecvd[x] = no
    /\ pDecision' = [pDecision EXCEPT ![x] = abort]
    /\ UNCHANGED <<pAlive, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cDecision, cFaulty, cSent>>

DecideOnBroadcast(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ cSent[x] # notsent
    /\ pDecision' = [pDecision EXCEPT ![x] = cSent[x]]
    /\ UNCHANGED <<pAlive, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cDecision, cFaulty, cSent>>

ParticipantDie(x) ==
    /\ pAlive[x]
    /\ pAlive' = [pAlive EXCEPT ![x] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![x] = TRUE]
    /\ UNCHANGED <<pDecision, pVote, pRequested, pRecvd,
                   cAlive, cDecision, cFaulty, cSent>>

SendVote(x) ==
    /\ pAlive[x]
    /\ pRequested[x]
    /\ pRecvd[x] = waiting
    /\ pRecvd' = [pRecvd EXCEPT ![x] = pVote[x]]
    /\ UNCHANGED <<pAlive, pDecision, pFaulty, pVote,
                   pRequested, cAlive, cDecision, cFaulty, cSent>>

AbortOnNoReq(x) ==
    /\ pAlive[x]
    /\ pDecision[x] = undecided
    /\ ~pRequested[x]
    /\ ~cAlive
    /\ pDecision' = [pDecision EXCEPT ![x] = abort]
    /\ UNCHANGED <<pAlive, pFaulty, pVote,
                   pRequested, pRecvd, cAlive, cDecision, cFaulty, cSent>>

Next ==
    \/ \E x \in participants : SendReq(x)
    \/ \E x \in participants : RecvVote(x)
    \/ \E x \in participants : DetectFault(x)
    \/ MakeDecision
    \/ \E x \in participants : BroadcastDecision(x)
    \/ CoordDie
    \/ \E x \in participants : AbortOnNoVote(x)
    \/ \E x \in participants : DecideOnBroadcast(x)
    \/ \E x \in participants : ParticipantDie(x)
    \/ \E x \in participants : SendVote(x)
    \/ \E x \in participants : AbortOnNoReq(x)

\* Participant progress actions are weakly fair so a participant that keeps being
\* asked to vote eventually sends that vote. Coordinator progress actions are
\* weakly fair so a coordinator that stays alive eventually reaches a decision.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A x \in participants :
        /\ WF_vars(SendVote(x))
        /\ WF_vars(DecideOnBroadcast(x))
        /\ WF_vars(AbortOnNoVote(x))
        /\ WF_vars(AbortOnNoReq(x))
    /\ WF_vars(MakeDecision)
    /\ WF_vars(CoordDie)

\* Safety: agreement, commit/abort validity, and irrevocability.
Agree ==
    \A a, b \in participants :
        ~ (pDecision[a] = commit /\ pDecision[b] = abort)

CommitValid ==
    \A x \in participants :
        (pDecision[x] = commit) => (\A y \in participants : pVote[y] = yes)

AbortValid ==
    \A x \in participants :
        (pDecision[x] = abort) =>
            \/ \E y \in participants : pVote[y] = no
            \/ \E y \in participants : pFaulty[y]
            \/ cFaulty

Irreversible ==
    \A x \in participants :
        /\ (pDecision[x] = commit) => (pDecision[x] = commit)
        /\ (pDecision[x] = abort) => (pDecision[x] = abort)

\* Liveness: either everyone decides, or the coordinator or a participant dies.
DecideHalt ==
    <>(\A x \in participants : pDecision[x] # undecided) \/ cFaulty
        \/ \E x \in participants : pFaulty[x]

====