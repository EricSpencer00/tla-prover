---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSent,
          coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSent,
           coordReq, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pSent \in [participants -> BOOLEAN]
    /\ coordReq \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [pa \in participants |-> TRUE]
    /\ pDecision = [pa \in participants |-> undecided]
    /\ pFaulty = [pa \in participants |-> FALSE]
    /\ pSent = [pa \in participants |-> FALSE]
    /\ coordReq = [pa \in participants |-> FALSE]
    /\ coordRecv = [pa \in participants |-> waiting]
    /\ coordSent = [pa \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* Coordinator actions
SendRequest(pa) ==
    /\ coordAlive
    /\ ~coordReq[pa]
    /\ coordReq' = [coordReq EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordRecv, coordSent, coordDecision, coordFaulty>>

RecvVote(pa) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReq[pa]
    /\ coordRecv[pa] = waiting
    /\ pSent[pa]
    /\ coordRecv' = [coordRecv EXCEPT ![pa] = pVote[pa]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordReq, coordSent, coordDecision, coordFaulty>>

DetectFault(pa) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordReq[pa]
    /\ coordRecv[pa] = waiting
    /\ ~pAlive[pa]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

MakeDecision ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A pa \in participants : coordRecv[pa] # waiting
    /\ coordDecision' = IF \A pa \in participants : coordRecv[pa] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(pa) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[pa] = notsent
    /\ coordSent' = [coordSent EXCEPT ![pa] = coordDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordReq, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordDecision>>

\* Participant actions
SendVote(pa) ==
    /\ pAlive[pa]
    /\ coordReq[pa]
    /\ ~pSent[pa]
    /\ pSent' = [pSent EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                  coordReq, coordRecv, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

AbortOnVote(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ pSent[pa]
    /\ pVote[pa] = no
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

AbortOnTimeout(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ ~coordAlive
    /\ ~coordReq[pa]
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

DecideFromCoord(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ coordSent[pa] # notsent
    /\ pDecision' = [pDecision EXCEPT ![pa] = coordSent[pa]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSent,
                  coordReq, coordRecv, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

PartDie(pa) ==
    /\ pAlive[pa]
    /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pDecision, pSent,
                  coordReq, coordRecv, coordSent, coordDecision,
                  coordAlive, coordFaulty>>

CoordinatorProgress ==
    \/ \E pa \in participants : SendRequest(pa)
    \/ \E pa \in participants : RecvVote(pa)
    \/ \E pa \in participants : DetectFault(pa)
    \/ MakeDecision
    \/ \E pa \in participants : BroadcastDecision(pa)

ParticipantProgress ==
    \/ \E pa \in participants : SendVote(pa)
    \/ \E pa \in participants : AbortOnVote(pa)
    \/ \E pa \in participants : AbortOnTimeout(pa)
    \/ \E pa \in participants : DecideFromCoord(pa)

Next ==
    \/ CoordinatorProgress \/ ParticipantProgress
    \/ CoordDie \/ \E pa \in participants : PartDie(pa)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorProgress) /\ WF_vars(ParticipantProgress)

\* Safety: no two participants ever decide differently, and decisions are
\* justified by the votes and failures that occurred.
Agreement ==
    \A pa \in participants : \A qa \in participants :
        (pDecision[pa] = commit /\ pDecision[qa] = abort) => FALSE

CommitValid ==
    \A pa \in participants : pDecision[pa] = commit => (\A qa \in participants : pVote[qa] = yes)

AbortValid ==
    \A pa \in participants : pDecision[pa] = abort =>
        \/ \E qa \in participants : pVote[qa] = no
        \/ \E qa \in participants : pFaulty[qa]
        \/ coordFaulty

Irreversible ==
    \A pa \in participants :
        (pDecision[pa] = commit => [x \in participants |-> pDecision[x]] = [x \in participants |-> IF x = pa THEN commit ELSE pDecision[x]]) /\
        (pDecision[pa] = abort => [x \in participants |-> pDecision[x]] = [x \in participants |-> IF x = pa THEN abort ELSE pDecision[x]])

\* Liveness: the protocol is not non-blocking -- participants may be left
\* undecided indefinitely -- but it does always reach a terminal shape.
EventuallyDecideOrFail ==
    <>(\A pa \in participants : pDecision[pa] # undecided) \/ <>(\E pa \in participants : pFaulty[pa]) \/ coordFaulty

====