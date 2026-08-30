---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordinatorRequested, coordinatorReceived, coordinatorSent,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordinatorRequested, coordinatorReceived, coordinatorSent,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

TypeOK ==
    /\ participantVote \in [participants -> {yes, no}]
    /\ participantAlive \in [participants -> BOOLEAN]
    /\ participantDecision \in [participants -> {undecided, commit, abort}]
    /\ participantFaulty \in [participants -> BOOLEAN]
    /\ participantSent \in [participants -> BOOLEAN]
    /\ coordinatorRequested \in [participants -> BOOLEAN]
    /\ coordinatorReceived \in [participants -> {waiting, yes, no}]
    /\ coordinatorSent \in [participants -> {notsent, commit, abort}]
    /\ coordinatorDecision \in {undecided, commit, abort}
    /\ coordinatorAlive \in BOOLEAN
    /\ coordinatorFaulty \in BOOLEAN

Init ==
    /\ \E v \in {yes, no} : participantVote = [p \in participants |-> v]
    /\ participantAlive = [p \in participants |-> TRUE]
    /\ participantDecision = [p \in participants |-> undecided]
    /\ participantFaulty = [p \in participants |-> FALSE]
    /\ participantSent = [p \in participants |-> FALSE]
    /\ coordinatorRequested = [p \in participants |-> FALSE]
    /\ coordinatorReceived = [p \in participants |-> waiting]
    /\ coordinatorSent = [p \in participants |-> notsent]
    /\ coordinatorDecision = undecided
    /\ coordinatorAlive = TRUE
    /\ coordinatorFaulty = FALSE

SendVoteRequest(p) ==
    /\ coordinatorAlive
    /\ ~coordinatorRequested[p]
    /\ coordinatorRequested' = [coordinatorRequested EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorReceived,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

ReceiveVote(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ coordinatorRequested[p]
    /\ coordinatorReceived[p] = waiting
    /\ participantSent[p]
    /\ coordinatorReceived' = [coordinatorReceived EXCEPT ![p] = participantVote[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorRequested,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

DetectFault(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ coordinatorRequested[p]
    /\ coordinatorReceived[p] = waiting
    /\ ~participantAlive[p]
    /\ coordinatorDecision' = abort
    /\ coordinatorSent' = [q \in participants |-> abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorRequested,
                   coordinatorReceived, coordinatorAlive, coordinatorFaulty>>

MakeDecision ==
    /\ coordinatorAlive
    /\ coordinatorDecision = undecided
    /\ \A p \in participants : coordinatorRequested[p]
    /\ \A p \in participants : coordinatorReceived[p] # waiting
    /\ coordinatorDecision' = IF \A p \in participants : coordinatorReceived[p] = yes
                                 THEN commit ELSE abort
    /\ coordinatorSent' = [q \in participants |-> IF \A p \in participants : coordinatorReceived[p] = yes THEN commit ELSE abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorRequested,
                   coordinatorReceived, coordinatorAlive, coordinatorFaulty>>

BroadcastDecision(p) ==
    /\ coordinatorAlive
    /\ coordinatorDecision # undecided
    /\ coordinatorSent[p] = notsent
    /\ coordinatorSent' = [coordinatorSent EXCEPT ![p] = coordinatorDecision]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorRequested,
                   coordinatorReceived, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

CoordinatorDie ==
    /\ coordinatorAlive
    /\ coordinatorAlive' = FALSE
    /\ coordinatorFaulty' = TRUE
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, participantSent, coordinatorRequested,
                   coordinatorReceived, coordinatorSent, coordinatorDecision>>

SendVote(p) ==
    /\ participantAlive[p]
    /\ coordinatorRequested[p]
    /\ ~participantSent[p]
    /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                   participantFaulty, coordinatorRequested, coordinatorReceived,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

AbortOnVote(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ participantSent[p]
    /\ participantVote[p] = no
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent, coordinatorRequested, coordinatorReceived,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

AbortOnTimeout(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ ~coordinatorAlive
    /\ ~coordinatorRequested[p]
    /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent, coordinatorRequested, coordinatorReceived,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

DecideFromBroadcast(p) ==
    /\ participantAlive[p]
    /\ participantDecision[p] = undecided
    /\ coordinatorSent[p] # notsent
    /\ participantDecision' = [participantDecision EXCEPT ![p] = coordinatorSent[p]]
    /\ UNCHANGED <<participantVote, participantAlive, participantFaulty,
                   participantSent, coordinatorRequested, coordinatorReceived,
                   coordinatorSent, coordinatorDecision, coordinatorAlive,
                   coordinatorFaulty>>

ParticipantDie(p) ==
    /\ participantAlive[p]
    /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
    /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<participantVote, participantDecision, participantSent,
                   coordinatorRequested, coordinatorReceived, coordinatorSent,
                   coordinatorDecision, coordinatorAlive, coordinatorFaulty>>

Next ==
    \/ MakeDecision
    \/ CoordinatorDie
    \/ \E p \in participants :
           SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectFault(p) \/ BroadcastDecision(p)
           \/ SendVote(p) \/ AbortOnVote(p) \/ AbortOnTimeout(p) \/ DecideFromBroadcast(p)
           \/ ParticipantDie(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in participants : BroadcastDecision(p))
    /\ WF_vars(\E p \in participants : DecideFromBroadcast(p))

Agreement ==
    \A p \in participants : \A q \in participants :
        ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

CommitValidity ==
    \A p \in participants : participantDecision[p] = commit => (\A q \in participants : participantVote[q] = yes)

AbortValidity ==
    \E p \in participants :
        participantDecision[p] = abort =>
            (\E q \in participants : participantVote[q] = no) \/ (\E q \in participants : participantFaulty[q]) \/ coordinatorFaulty

Irrevocability ==
    \A p \in participants :
        /\ (participantDecision[p] = commit) => (participantDecision' = [participantDecision EXCEPT ![p] = commit])
        /\ (participantDecision[p] = abort) => (participantDecision' = [participantDecision EXCEPT ![p] = abort])

Termination ==
    \A p \in participants :
        (participantDecision[p] = undecided) ~> (participantDecision[p] # undecided)

Properties == Agreement /\ CommitValidity /\ AbortValidity /\ Irrevocability

====