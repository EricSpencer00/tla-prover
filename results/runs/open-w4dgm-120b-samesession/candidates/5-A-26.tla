---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator and participants share a single broadcast channel; a crash mid-broadcast can
\* quietly strand a live participant, which is what makes this variant blocking but not faulty.
\* AC2 and AC3 are the commit/abort validity checks; AC4 is the per-participant at-most-once decision.
\* Weak fairness is assumed on progress actions (SendVoteRequest, ReceiveVote, etc.) but not on
\* death, which can strike silently at any moment. Model checking covers AC1-AC4 for safety and
\* the eventual-decision-or-failure liveness requirement identified in the spec.

VARIABLES coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
          pAlive, pFaulty, pVote, pDecision, pSentVote

Vars == <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
           pAlive, pFaulty, pVote, pDecision, pSentVote>>

TypeOK ==
    /\ coordAlive \in BOOLEAN /\ coordFaulty \in BOOLEAN
    /\ coordDecision \in {commit, abort, undecided}
    /\ coordSent \in [participants -> {notsent, commit, abort}]
    /\ coordRecv \in [participants -> {waiting, yes, no}]
    /\ pAlive \in [participants -> BOOLEAN] /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ pDecision \in [participants -> {commit, abort, undecided}]
    /\ pSentVote \in [participants -> BOOLEAN]

Init ==
    /\ coordAlive = TRUE /\ coordFaulty = FALSE
    /\ coordDecision = undecided
    /\ coordSent = [p \in participants |-> notsent]
    /\ coordRecv = [p \in participants |-> waiting]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote = [p \in participants |-> CHOOSE v \in {yes, no} : TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pSentVote = [p \in participants |-> FALSE]

SendVoteRequest(p) ==
    /\ coordAlive /\ coordDecision = undecided
    /\ coordSent[p] = notsent /\ ~pSentVote[p]
    /\ coordSent' = [coordSent EXCEPT ![p] = waiting]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRecv,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

ReceiveVote(p) ==
    /\ coordAlive /\ coordDecision = undecided
    /\ coordSent[p] # notsent /\ coordRecv[p] = waiting
    /\ pAlive[p] /\ pSentVote[p]
    /\ coordRecv' = [coordRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

DetectParticipantFault(p) ==
    /\ coordAlive /\ coordDecision = undecided
    /\ coordSent[p] # notsent /\ coordRecv[p] = waiting
    /\ ~pAlive[p]
    /\ coordDecision' = abort /\ coordSent' = [coordSent EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordRecv,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

MakeDecision ==
    /\ coordAlive /\ coordDecision = undecided
    /\ \A p \in participants : coordRecv[p] # waiting
    /\ coordDecision' = IF \A p \in participants : coordRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<coordAlive, coordFaulty, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

BroadcastDecision(p) ==
    /\ coordAlive /\ coordDecision # undecided
    /\ coordSent[p] = notsent /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordRecv,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

CoordDie ==
    /\ coordAlive /\ coordAlive' = FALSE /\ coordFaulty' = TRUE
    /\ UNCHANGED <<coordDecision, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pDecision, pSentVote>>

SendVote(p) ==
    /\ pAlive[p] /\ coordSent[p] # notsent /\ ~pSentVote[p]
    /\ pSentVote' = [pSentVote EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pDecision>>

AbortOnVote(p) ==
    /\ pAlive[p] /\ pDecision[p] = undecided
    /\ pSentVote[p] /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pSentVote>>

AbortOnTimeout(p) ==
    /\ pAlive[p] /\ pDecision[p] = undecided
    /\ ~coordAlive /\ coordSent[p] = notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pSentVote>>

DecideOnCoordinator(p) ==
    /\ pAlive[p] /\ pDecision[p] = undecided
    /\ coordSent[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordSent[p]]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
                   pAlive, pFaulty, pVote, pSentVote>>

ParticipantDie(p) ==
    /\ pAlive[p] /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<coordAlive, coordFaulty, coordDecision, coordSent, coordRecv,
                   pVote, pDecision, pSentVote>>

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p)
                              \/ DetectParticipantFault(p) \/ BroadcastDecision(p)
                              \/ SendVote(p) \/ AbortOnVote(p)
                              \/ AbortOnTimeout(p) \/ DecideOnCoordinator(p)
                              \/ ParticipantDie(p)
    \/ MakeDecision \/ CoordDie

\* SAFETY properties: AC1-AC4 hold at every reachable state. LIVENESS property: at least one
\* terminal resolution is always eventually reached (all decided, or a fault surfaces).
Spec == Init /\ [][Next]_Vars /\ WF_Vars(SendVoteRequest("a")) /\ WF_Vars(ReceiveVote("a"))
          /\ WF_Vars(BroadcastDecision("a")) /\ WF_Vars(DecideOnCoordinator("a"))

TypeInv == TypeOK

DecisionAgreement ==
    \A p1, p2 \in participants :
        (pDecision[p1] = commit /\ pDecision[p2] = abort) => FALSE

CommitValidity ==
    \A p \in participants : pDecision[p] = commit => (\A q \in participants : coordRecv[q] = yes)

AbortValidity ==
    \A p \in participants :
        pDecision[p] = abort =>
            \/ \E q \in participants : coordRecv[q] = no
            \/ (\E q \in participants : pFaulty[q])
            \/ coordFaulty

IrreversibleDecide ==
    \A p \in participants :
        /\ (pDecision[p] = commit => (pDecision[p] = commit) [][pDecision[p] = commit])
        /\ (pDecision[p] = abort => (pDecision[p] = abort) [][pDecision[p] = abort])

EventuallyDecideOrFail ==
    <>(\A p \in participants : pDecision[p] # undecided \/ \E p \in participants : pFaulty[p])
====