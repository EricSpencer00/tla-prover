---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Variables are grouped per actor: coordinator state plus one tuple per participant.
VARIABLES cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv, coordinatorBroadcast,
         pAlive, pDecision, pFaulty, pVote, participantSent

vars == <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
          coordinatorBroadcast, pAlive, pDecision, pFaulty, pVote, participantSent>>

TypeInv ==
    /\ cAlive \in BOOLEAN
    /\ cDecision \in {undecided, commit, abort}
    /\ cFaulty \in BOOLEAN
    /\ coordinatorSent \in [participants -> BOOLEAN]
    /\ coordinatorRecv \in [participants -> {yes, no, waiting}]
    /\ coordinatorBroadcast \in [participants -> {commit, abort, notsent}]
    /\ pAlive \in [participants -> BOOLEAN]
    /\ pDecision \in [participants -> {undecided, commit, abort}]
    /\ pFaulty \in [participants -> BOOLEAN]
    /\ pVote \in [participants -> {yes, no}]
    /\ participantSent \in [participants -> BOOLEAN]

Init ==
    /\ cAlive = TRUE
    /\ cDecision = undecided
    /\ cFaulty = FALSE
    /\ coordinatorSent = [p \in participants |-> FALSE]
    /\ coordinatorRecv = [p \in participants |-> waiting]
    /\ coordinatorBroadcast = [p \in participants |-> notsent]
    /\ pAlive = [p \in participants |-> TRUE]
    /\ pDecision = [p \in participants |-> undecided]
    /\ pFaulty = [p \in participants |-> FALSE]
    /\ pVote \in [participants -> {yes, no}]
    /\ participantSent = [p \in participants |-> FALSE]

SendVoteRequest(p) ==
    /\ cAlive
    /\ ~coordinatorSent[p]
    /\ coordinatorSent' = [coordinatorSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorRecv, coordinatorBroadcast,
                   pAlive, pDecision, pFaulty, pVote, participantSent>>

\* The coordinator receives a vote only if that participant actually sent it.
ReceiveVote(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ coordinatorSent[p]
    /\ coordinatorRecv[p] = waiting
    /\ participantSent[p]
    /\ coordinatorRecv' = [coordinatorRecv EXCEPT ![p] = pVote[p]]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorBroadcast,
                   pAlive, pDecision, pFaulty, pVote, participantSent>>

DetectFault(p) ==
    /\ cAlive
    /\ cDecision = undecided
    /\ coordinatorSent[p]
    /\ coordinatorRecv[p] = waiting
    /\ cFaulty = FALSE
    /\ pAlive[p] = FALSE
    /\ cDecision' = abort
    /\ UNCHANGED <<cAlive, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pDecision, pFaulty, pVote, participantSent>>

MakeDecision ==
    /\ cAlive
    /\ cDecision = undecided
    /\ \A p \in participants : coordinatorRecv[p] # waiting
    /\ cDecision' = IF \A p \in participants : coordinatorRecv[p] = yes THEN commit ELSE abort
    /\ UNCHANGED <<cAlive, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pDecision, pFaulty, pVote, participantSent>>

\* Simple broadcast: a decision is sent to each participant separately and in sequence.
Broadcast(p) ==
    /\ cAlive
    /\ cDecision # undecided
    /\ coordinatorBroadcast[p] = notsent
    /\ coordinatorBroadcast' = [coordinatorBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   pAlive, pDecision, pFaulty, pVote, participantSent>>

DieCoordinator ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED <<cDecision, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pDecision, pFaulty, pVote, participantSent>>

SendVote(p) ==
    /\ pAlive[p]
    /\ coordinatorSent[p]
    /\ participantSent[p] = FALSE
    /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pDecision, pFaulty, pVote>>

AbortOnVote(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ participantSent[p]
    /\ pVote[p] = no
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pFaulty, pVote, participantSent>>

AbortOnTimeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordinatorSent[p] = FALSE
    /\ cAlive = FALSE
    /\ pDecision' = [pDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pFaulty, pVote, participantSent>>

DecideOnBroadcast(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = undecided
    /\ coordinatorBroadcast[p] # notsent
    /\ pDecision' = [pDecision EXCEPT ![p] = coordinatorBroadcast[p]]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pAlive, pFaulty, pVote, participantSent>>

DieParticipant(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cAlive, cDecision, cFaulty, coordinatorSent, coordinatorRecv,
                   coordinatorBroadcast, pDecision, pVote, participantSent>>

CoordinatorStep == MakeDecision \/ DieCoordinator
ParticipantStep == AbortOnVote \/ AbortOnTimeout \/ DecideOnBroadcast
CoordinatedStep == CoordinatorStep \/ ParticipantStep

Next ==
    \/ \E p \in participants : SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ Broadcast(p) \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideOnBroadcast(p) \/ DieParticipant(p)
    \/ CoordinatorStep

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatedStep)

\* Safety: no diverging decisions, and decisions are only ever made on a unanimous
\* yes-vote or a detected fault, and each participant decides at most once.
NoDivergence ==
    \A p, q \in participants : ~(pDecision[p] = commit /\ pDecision[q] = abort)

CommitValidity ==
    \A p \in participants : pDecision[p] = commit => \A q \in participants : pVote[q] = yes

AbortValidity ==
    \A p \in participants : pDecision[p] = abort =>
        \/ \E q \in participants : pVote[q] = no
        \/ \E q \in participants : pFaulty[q] = TRUE
        \/ cFaulty = TRUE

CommitIrreversible ==
    \A p \in participants : pDecision[p] = commit ~> (pDecision[p] = commit)

AbortIrreversible ==
    \A p \in participants : pDecision[p] = abort ~> (pDecision[p] = abort)

\* Liveness: every participant gets a decision or some actor fails.
DecideOrFault ==
    <>(\A p \in participants : pDecision[p] # undecided) \/ <>(\E p \in participants : pFaulty[p]) \/ <>(cFaulty)

====