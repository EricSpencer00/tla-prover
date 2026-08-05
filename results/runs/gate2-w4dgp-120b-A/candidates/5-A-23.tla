---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSentVote, coordinatorSentRequest, coordinatorVote, coordinatorSent,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty

vars == << participantVote, participantAlive, participantDecision, participantFaulty,
           participantSentVote, coordinatorSentRequest, coordinatorVote, coordinatorSent,
           coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

TypeInv ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSentVote \in [participants -> BOOLEAN]
  /\ coordinatorSentRequest \in [participants -> BOOLEAN]
  /\ coordinatorVote \in [participants -> {yes, no, waiting}]
  /\ coordinatorSent \in [participants -> {notsent} \cup {commit, abort}]
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN

Init ==
  /\ participantVote = [p \in participants |-> IF (Cardinality(participants) % 2 = 0) THEN yes ELSE no]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSentVote = [p \in participants |-> FALSE]
  /\ coordinatorSentRequest = [p \in participants |-> FALSE]
  /\ coordinatorVote = [p \in participants |-> waiting]
  /\ coordinatorSent = [p \in participants |-> notsent]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE

SendRequest(p) ==
  /\ coordinatorAlive
  /\ ~coordinatorSentRequest[p]
  /\ coordinatorSentRequest' = [coordinatorSentRequest EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ReceiveVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A q \in participants : coordinatorSentRequest[q]
  /\ coordinatorVote[p] = waiting
  /\ participantSentVote[p]
  /\ coordinatorVote' = [coordinatorVote EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorSentRequest, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

DetectParticipantFault(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ coordinatorSentRequest[p]
  /\ coordinatorVote[p] = waiting
  /\ ~participantAlive[p]
  /\ coordinatorDecision' = abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorSentRequest, coordinatorVote,
                 coordinatorSent, coordinatorAlive, coordinatorFaulty >>

MakeDecision ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants : coordinatorVote[p] # waiting
  /\ coordinatorDecision' =
       IF \A p \in participants : coordinatorVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorAlive, coordinatorFaulty >>

BroadcastDecision(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision # undecided
  /\ coordinatorSent[p] = notsent
  /\ coordinatorSent' = [coordinatorSent EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorSentRequest, coordinatorVote,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

CoordinatorDie ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSentVote, coordinatorSentRequest, coordinatorVote,
                 coordinatorSent, coordinatorDecision >>

SendVote(p) ==
  /\ participantAlive[p]
  /\ coordinatorSentRequest[p]
  /\ participantSentVote[p] = FALSE
  /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                 coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ParticipantAbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSentVote[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty, participantSentVote,
                 coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ParticipantAbortOnTimeoutForRequest(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordinatorAlive = FALSE
  /\ coordinatorSentRequest[p] = FALSE
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty, participantSentVote,
                 coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

DecideOnCoordinatorBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordinatorSent[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordinatorSent[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty, participantSentVote,
                 coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ParticipantDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantDecision, participantSentVote,
                 coordinatorSentRequest, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ParticipantProgress(p) ==
  \/ SendVote(p)
  \/ ParticipantAbortOnVote(p)
  \/ ParticipantAbortOnTimeoutForRequest(p)
  \/ DecideOnCoordinatorBroadcast(p)

CoordinatorProgress(p) ==
  \/ SendRequest(p)
  \/ ReceiveVote(p)
  \/ DetectParticipantFault(p)
  \/ BroadcastDecision(p)

Next ==
  \/ MakeDecision
  \/ CoordinatorDie
  \/ \E p \in participants : CoordinatorProgress(p) \/ ParticipantProgress(p) \/ ParticipantDie(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : SF_vars(CoordinatorProgress(p))
  /\ \A p \in participants : SF_vars(ParticipantProgress(p))

AC1 ==
  ~ \E p1 \in participants, p2 \in participants :
       (participantDecision[p1] = commit) /\ (participantDecision[p2] = abort)

AC2 ==
  \A p \in participants : (participantDecision[p] = commit) => (participantVote[p] = yes)

AC3 ==
  \A p \in participants :
    (participantDecision[p] = abort) =>
      (\E q \in participants : (participantVote[q] = no) \/ participantFaulty[q] \/ coordinatorFaulty)

AC4 ==
  \A p \in participants :
    /\ (participantDecision[p] = commit) ~> (participantDecision[p] = abort)
    /\ (participantDecision[p] = abort) ~> (participantDecision[p] = commit)

DecidedOrSomeFault ==
  <>(\A p \in participants : participantDecision[p] # undecided) \/ (\E p \in participants : participantFaulty[p]) \/ coordinatorFaulty

====