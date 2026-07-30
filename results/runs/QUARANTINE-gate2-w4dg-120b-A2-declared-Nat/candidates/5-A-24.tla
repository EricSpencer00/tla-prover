---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES pVote, pAlive, pDecision, pFaulty, pSentVote,
         coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty

vars == <<pVote, pAlive, pDecision, pFaulty, pSentVote,
           coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

TypeInv ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in BOOLEAN
    /\ pSentVote \in [participants -> BOOLEAN]
    /\ coordRequested \in [participants -> BOOLEAN]
    /\ coordRecv \in [participants -> {yes, no, waiting}]
    /\ coordSent \in [participants -> {commit, abort, notsent}]
    /\ coordDecision \in {undecided, commit, abort}
    /\ coordAlive \in BOOLEAN
    /\ coordFaulty \in BOOLEAN

\* The coordinator starts by sending vote requests; participants then send
\* votes, after which the coordinator decides and broadcasts by simple broadcast.
Init ==
    /\ pVote \in [participants -> {yes, no}]
    /\ pAlive = [pa \in participants |-> TRUE]
    /\ pDecision = [pa \in participants |-> undecided]
    /\ pFaulty = FALSE
    /\ pSentVote = [pa \in participants |-> FALSE]
    /\ coordRequested = [pa \in participants |-> FALSE]
    /\ coordRecv = [pa \in participants |-> waiting]
    /\ coordSent = [pa \in participants |-> notsent]
    /\ coordDecision = undecided
    /\ coordAlive = TRUE
    /\ coordFaulty = FALSE

\* The coordinator broadcasts each decision to participants one at a time.
CoordRequest(pa) ==
    /\ coordAlive
    /\ ~coordRequested[pa]
    /\ coordRequested' = [coordRequested EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRecv, coordSent, coordDecision, coordFaulty>>

CoordRecvVote(pa) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[pa]
    /\ coordRecv[pa] = waiting
    /\ pSentVote[pa]
    /\ coordRecv' = [coordRecv EXCEPT ![pa] = pVote[pa]]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRequested, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Failure detection here is magical: a crashed participant's missing vote
\* is detected immediately, which forces the coordinator to abort.
CoordDetectFault(pa) ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ coordRequested[pa]
    /\ coordRecv[pa] = waiting
    /\ ~pAlive[pa]
    /\ coordDecision' = abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordAlive, coordFaulty>>

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = undecided
    /\ \A pa \in participants : coordRecv[pa] # waiting
    /\ coordDecision' = IF \A pa \in participants : coordRecv[pa] = yes THEN commit ELSE abort
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordAlive, coordFaulty>>

CoordBroadcast(pa) ==
    /\ coordAlive
    /\ coordDecision # undecided
    /\ coordSent[pa] = notsent
    /\ coordSent' = [coordSent EXCEPT ![pa] = coordDecision]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordDecision, coordAlive, coordFaulty>>

CoordDie ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ coordFaulty' = TRUE
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordDecision>>

\* A participant holds back its vote until the coordinator actually asks for it.
SendVote(pa) ==
    /\ pAlive[pa]
    /\ coordRequested[pa]
    /\ ~pSentVote[pa]
    /\ pSentVote' = [pSentVote EXCEPT ![pa] = TRUE]
    /\ UNCHANGED <<pVote, pAlive, pDecision, pFaulty,
                  coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ pSentVote[pa]
    /\ pVote[pa] = no
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnTimeout(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ ~coordRequested[pa]
    /\ ~coordAlive
    /\ pDecision' = [pDecision EXCEPT ![pa] = abort]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(pa) ==
    /\ pAlive[pa]
    /\ pDecision[pa] = undecided
    /\ coordSent[pa] # notsent
    /\ pDecision' = [pDecision EXCEPT ![pa] = coordSent[pa]]
    /\ UNCHANGED <<pVote, pAlive, pFaulty, pSentVote,
                  coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

ParticipantDie(pa) ==
    /\ pAlive[pa]
    /\ pAlive' = [pAlive EXCEPT ![pa] = FALSE]
    /\ pFaulty' = TRUE
    /\ UNCHANGED <<pVote, pDecision, pSentVote,
                  coordRequested, coordRecv, coordSent, coordDecision, coordAlive, coordFaulty>>

\* Weak fairness (outside of death transitions) guarantees each participant and
\* the coordinator eventually get a chance to make progress.
Next ==
    \/ \E pa \in participants : CoordRequest(pa)
    \/ \E pa \in participants : CoordRecvVote(pa)
    \/ \E pa \in participants : CoordDetectFault(pa)
    \/ CoordDecide
    \/ \E pa \in participants : CoordBroadcast(pa)
    \/ CoordDie
    \/ \E pa \in participants : SendVote(pa)
    \/ \E pa \in participants : AbortOnVote(pa)
    \/ \E pa \in participants : AbortOnTimeout(pa)
    \/ \E pa \in participants : DecideOnBroadcast(pa)
    \/ \E pa \in participants : ParticipantDie(pa)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E pa \in participants : SendVote(pa))
    /\ WF_vars(\E pa \in participants : AbortOnVote(pa))
    /\ WF_vars(\E pa \in participants : DecideOnBroadcast(pa))
    /\ WF_vars(CoordDecide)

\* Safety: all participants that decide must agree on commit versus abort.
AgreementConsistency ==
    ~ \E pa, pb \in participants :
        /\ pDecision[pa] = commit
        /\ pDecision[pb] = abort
    /\ UNCHANGED vars

CommitValidity ==
    ~ \E pa \in participants :
        pDecision[pa] = commit /\ \E pb \in participants : pVote[pb] = no
    /\ UNCHANGED vars

AbortValidity ==
    ~ \E pa \in participants :
        pDecision[pa] = abort /\ (\A pb \in participants : pVote[pb] = yes) /\ ~pFaulty
    /\ UNCHANGED vars

Irreversibility ==
    /\ \A pa \in participants : (pDecision[pa] = commit) ~> (pDecision[pa] = commit)
    /\ \A pa \in participants : (pDecision[pa] = abort) ~> (pDecision[pa] = abort)
    /\ UNCHANGED vars

\* Liveness: either every participant arrives at a decision, or a fault is
\* present to explain why the simple broadcast cannot finish.
EventualDecision ==
    <>(\A pa \in participants : pDecision[pa] # undecided \/ pFaulty \/ coordFaulty)

====