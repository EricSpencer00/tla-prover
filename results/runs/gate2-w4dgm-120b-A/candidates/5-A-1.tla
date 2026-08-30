---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME yes # no /\ commit # abort /\ undecided # commit /\ undecided # abort

VARIABLES pvote, palive, pdecided, pfaulty, pSentReq
Variable == { pvote, palive, pdecided, pfaulty, pSentReq }

CoordinatorVars == {cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast}
VARIABLES cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast

vars == << pvote, palive, pdecided, pfaulty, pSentReq,
           cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

TypeOK ==
    /\ pvote \in [participants -> {yes, no}]
    /\ palive \in [participants -> BOOLEAN]
    /\ pdecided \in [participants -> {undecided, commit, abort}]
    /\ pfaulty \in [participants -> BOOLEAN]
    /\ pSentReq \in [participants -> BOOLEAN]
    /\ cAlive \in BOOLEAN
    /\ cFaulty \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cVoted \in [participants -> {waiting, yes, no}]
    /\ cReplied \in [participants -> {notsent, commit, abort}]
    /\ cBroadcast \in [participants -> {notsent, commit, abort}]

\* A coordinator crash can leave undecided participants forever undecided, so
\* the AC3 liveness property below is framed as "eventually everyone decides
\* OR someone is faulty", which simple broadcast cannot guarantee is always
\* everyone deciding.
Init ==
    /\ \E v \in {yes, no} : pvote = [p \in participants |-> v]
    /\ palive = [p \in participants |-> TRUE]
    /\ pdecided = [p \in participants |-> undecided]
    /\ pfaulty = [p \in participants |-> FALSE]
    /\ pSentReq = [p \in participants |-> FALSE]
    /\ cAlive = TRUE
    /\ cFaulty = FALSE
    /\ cDecision = undecided
    /\ cVoted = [p \in participants |-> waiting]
    /\ cReplied = [p \in participants |-> notsent]
    /\ cBroadcast = [p \in participants |-> notsent]

SendRequest(p) ==
    /\ cAlive
    /\ ~cRequested[p]
    /\ cRequested' = [cRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

\* Tracks which participants the coordinator has actually requested.
cRequested == [p \in participants |-> pSentReq[p]]

ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVoted[p] = waiting
    /\ pSentReq[p]
    /\ cVoted' = [cVoted EXCEPT ![p] = pvote[p]]
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cAlive, cFaulty, cDecision, cReplied, cBroadcast >>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ cRequested[p]
    /\ cVoted[p] = waiting
    /\ ~palive[p]
    /\ pSentReq[p]
    /\ cDecision' = abort
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cAlive, cFaulty, cVoted, cReplied, cBroadcast >>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : cVoted[p] # waiting
    /\ cDecision' = IF \A p \in participants : cVoted[p] = yes THEN commit ELSE abort
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cAlive, cFaulty, cVoted, cReplied, cBroadcast >>

BroadcastDecision(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ cBroadcast[p] = notsent
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cAlive, cFaulty, cDecision, cVoted, cReplied >>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty, pSentReq,
                   cDecision, cVoted, cReplied, cBroadcast >>

SendVote(p) ==
    /\ palive[p]
    /\ cRequested[p]
    /\ ~pSentReq[p]
    /\ pSentReq' = [pSentReq EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pvote, palive, pdecided, pfaulty,
                   cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

AbortOnVote(p) ==
    /\ palive[p]
    /\ pdecided[p] = undecided
    /\ pSentReq[p]
    /\ pvote[p] = no
    /\ pdecided' = [pdecided EXCEPT ![p] = abort]
    /\ UNCHANGED << pvote, palive, pSentReq,
                   pfaulty, cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

AbortOnTimeout(p) ==
    /\ palive[p]
    /\ pdecided[p] = undecided
    /\ ~cAlive
    /\ ~pSentReq[p]
    /\ pdecided' = [pdecided EXCEPT ![p] = abort]
    /\ UNCHANGED << pvote, palive, pSentReq,
                   pfaulty, cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

DecideOnBroadcast(p) ==
    /\ palive[p]
    /\ pdecided[p] = undecided
    /\ cBroadcast[p] # notsent
    /\ pdecided' = [pdecided EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED << pvote, palive, pSentReq,
                   pfaulty, cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

DieParticipant(p) ==
    /\ palive[p]
    /\ palive' = [palive EXCEPT ![p] = FALSE]
    /\ pfaulty' = [pfaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pvote, pdecided, pSentReq,
                   cAlive, cFaulty, cDecision, cVoted, cReplied, cBroadcast >>

Next ==
    \/ MakeDecision
    \/ DieCoordinator
    \/ \E p \in participants :
         \/ SendRequest(p)
         \/ ReceiveVote(p)
         \/ DetectFault(p)
         \/ BroadcastDecision(p)
         \/ SendVote(p)
         \/ AbortOnVote(p)
         \/ AbortOnTimeout(p)
         \/ DecideOnBroadcast(p)
         \/ DieParticipant(p)

\* Non-blocking progress is only assumed for the non-failure actions; death
\* actions can always fire at any time, so they must never be assumed to
\* stop progress on their own.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(\E p \in participants : SendVote(p))
    /\ SF_vars(\E p \in participants : AbortOnVote(p))
    /\ SF_vars(\E p \in participants : DecideOnBroadcast(p))
    /\ WF_vars(\E p \in participants : SendRequest(p))
    /\ WF_vars(\E p \in participants : ReceiveVote(p))
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))

\* Safety: participants never disagree, and no decision can appear out of
\* thin air (commit needs unanimity, abort needs a no or a fault).
AC1 == \A x, y \in participants :
           (pdecided[x] = commit /\ pdecided[y] = abort) => FALSE

AC2 == (\E p \in participants : pdecided[p] = commit) =>
          (\A p \in participants : pvote[p] = yes)

AC3 == (\E p \in participants : pdecided[p] = abort) =>
          (\E p \in participants : pvote[p] = no \/ pfaulty[p] = TRUE)
             \/ cFaulty = TRUE

\* Liveness: the protocol is blocking, not stuck forever. Either everybody
\* decides, or a fault surfaces.
AC3Liveness == <>(\A p \in participants : pdecided[p] # undecided \/ cFaulty = TRUE)

TypeInv == TypeOK
====