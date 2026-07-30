---- MODULE ACP_NB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

ASSUME participants # {}
ASSUME yes # no
ASSUME undecided # commit
ASSUME commit # abort

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty
VARIABLES voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast
VARIABLES coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
          voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable>>

TypeInvNB ==
    /\ participantVote \in [participants -> {no, yes, undecided}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ voteSent \in [participants -> BOOLEAN]
    /\ coordinatorRequest \in {waiting, yes, no}
    /\ coordinatorVote \in {waiting, yes, no}
    /\ coordinatorBroadcast \in [participants -> {notsent, commit, abort}]
    /\ coordinatorDecision \in {notsent, commit, abort}
    /\ coordinatorAlive \in BOOLEAN
    /\ coordinatorFaulty \in BOOLEAN
    /\ participantTable \in [participants -> [participants -> {notsent, commit, abort}]]

InitNB ==
    /\ participantVote = [p \in participants |-> undecided]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ voteSent = [p \in participants |-> FALSE]
    /\ coordinatorRequest = waiting
    /\ coordinatorVote = waiting
    /\ coordinatorBroadcast = [p \in participants |-> notsent]
    /\ coordinatorDecision = notsent
    /\ coordinatorAlive = TRUE
    /\ coordinatorFaulty = FALSE
    /\ participantTable = [p \in participants |-> [q \in participants |-> notsent]]

SendRequest ==
    /\ coordinatorAlive
    /\ coordinatorRequest = waiting
    /\ coordinatorRequest' = yes
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable>>

SendVote(p) ==
    /\ coordinatorAlive
    /\ participantAlive[p]
    /\ ~voteSent[p]
    /\ coordinatorRequest # waiting
    /\ \E v \in {yes, no} : participantVote' = [participantVote EXCEPT ![p] = v]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantDecision, participantFaulty, coordinatorRequest,
                  coordinatorVote, coordinatorBroadcast, coordinatorDecision,
                  coordinatorAlive, coordinatorFaulty, participantTable>>

CoordinatorGetsVote ==
    /\ coordinatorAlive
    /\ coordinatorRequest # waiting
    /\ coordinatorVote = waiting
    /\ \E p \in participants :
        voteSent[p] /\ coordinatorVote' = participantVote[p]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable>>

DetectFault ==
    /\ coordinatorAlive
    /\ coordinatorVote = no
    /\ coordinatorAlive' = FALSE
    /\ coordinatorFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorFaulty, participantTable>>

MakeCoordinatorDecision ==
    /\ coordinatorAlive
    /\ coordinatorVote # waiting
    /\ coordinatorDecision = notsent
    /\ coordinatorDecision' = coordinatorVote
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorAlive, coordinatorFaulty, participantTable>>

BroadcastFromCoordinator ==
    /\ coordinatorAlive
    /\ coordinatorDecision # notsent
    /\ \E p \in participants :
        /\ coordinatorBroadcast[p] = notsent
        /\ coordinatorBroadcast' = [coordinatorBroadcast EXCEPT ![p] = coordinatorDecision]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorDecision,
                  coordinatorAlive, coordinatorFaulty, participantTable>>

ParticipantPredecideFromCoordinator(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordinatorBroadcast[p] # notsent
    /\ participantTable[p][p] = notsent
    /\ participantTable' = [participantTable EXCEPT ![p][p] = coordinatorBroadcast[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

ParticipantPredecideFromForward(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantTable[p][p] = notsent
    /\ \E q \in participants :
        /\ participantAlive[q]
        /\ participantTable[q][p] # notsent
        /\ participantTable' = [participantTable EXCEPT ![p][p] = participantTable[q][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

ForwardDecision(p, q) ==
    /\ participantAlive[p]
    /\ participantAlive[q]
    /\ p # q
    /\ participantTable[p][p] # notsent
    /\ participantTable[p][q] = notsent
    /\ participantTable' = [participantTable EXCEPT ![p][q] = participantTable[p][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

Decide(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ \A q \in participants : participantTable[p][q] # notsent
    /\ participantTable[p][p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = participantTable[p][p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable>>

ParticipantAbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordinatorAlive
    /\ \A q \in participants : coordinatorBroadcast[q] = notsent
    /\ \A q \in participants : ~participantAlive[q]
        => \A r \in participants : participantTable[q][r] = notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                  voteSent, coordinatorRequest, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty, participantTable>>

Die(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantDecision, voteSent, coordinatorRequest,
                  coordinatorVote, coordinatorBroadcast, coordinatorDecision,
                  coordinatorAlive, coordinatorFaulty, participantTable>>

NextNB ==
    \/ SendRequest \/ CoordinatorGetsVote \/ DetectFault \/ MakeCoordinatorDecision
    \/ BroadcastFromCoordinator
    \/ \E p \in participants : SendVote(p) \/ ParticipantPredecideFromCoordinator(p)
                            \/ ParticipantPredecideFromForward(p) \/ Decide(p)
                            \/ ParticipantAbortOnTimeout(p) \/ Die(p)
    \/ \E p \in participants, q \in participants : ForwardDecision(p, q)

SpecNB ==
    /\ InitNB
    /\ [][NextNB]_vars
    /\ WF_vars(\E p \in participants : SendVote(p) \/ Decide(p)
                 \/ ParticipantAbortOnTimeout(p) \/ Die(p))
    /\ WF_vars(\E p \in participants, q \in participants : ForwardDecision(p, q))

AgreementNB ==
    \A p \in participants : \A q \in participants :
        (participantDecision[p] = commit) => (participantDecision[q] # abort)

CommitValidityNB ==
    \A p \in participants : participantDecision[p] = commit => (\A q \in participants : participantVote[q] = yes)

AbortValidityNB ==
    \A p \in participants : participantDecision[p] = abort =>
        \/ \E q \in participants : participantVote[q] = no
        \/ \E q \in participants : participantFaulty[q]
        \/ coordinatorFaulty

IrrevocabilityNB ==
    \A p \in participants : participantDecision[p] # undecided
        => (participantDecision' = [participantDecision EXCEPT ![p] = participantDecision[p]])

LivenessNB ==
    \A p \in participants :
        <>(participantDecision[p] # undecided \/ participantFaulty[p] \/ coordinatorFaulty)

====