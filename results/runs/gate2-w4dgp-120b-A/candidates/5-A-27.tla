---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB). The coordinator gathers
\* votes from participants and then broadcasts a decision. Because the broadcast
\* is simple (one message at a time), a coordinator crash during broadcast can
\* stall some participants forever -- the protocol is blocking, not non-blocking.
\* The properties below capture safety (agreement and irrevocability) and the
\* weaker liveness that the system still guarantees despite possible blocking.
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordinatorRequested, coordinatorVote, coordinatorSent,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty

vars == << participantVote, participantAlive, participantDecision, participantFaulty,
           participantSent, coordinatorRequested, coordinatorVote, coordinatorSent,
           coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

TypeInv ==
  /\ coordinatorRequested \in [ participants -> BOOLEAN ]
  /\ coordinatorVote \in [ participants -> {yes, no, waiting} ]
  /\ coordinatorSent \in [ participants -> {notsent, commit, abort} ]
  /\ coordinatorDecision \in {commit, abort, undecided}
  /\ participantVote \in [ participants -> {yes, no} ]
  /\ participantAlive \in [ participants -> BOOLEAN ]
  /\ participantDecision \in [ participants -> {commit, abort, undecided} ]
  /\ participantFaulty \in [ participants -> BOOLEAN ]
  /\ participantSent \in [ participants -> BOOLEAN ]
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorFaulty \in BOOLEAN

AllVoteRequestsSent == \A p \in participants : coordinatorRequested[p]
AllVotesReceived == \A p \in participants : coordinatorVote[p] # waiting

Init ==
  /\ coordinatorRequested = [ p \in participants |-> FALSE ]
  /\ coordinatorVote = [ p \in participants |-> waiting ]
  /\ coordinatorSent = [ p \in participants |-> notsent ]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = TRUE
  /\ coordinatorFaulty = FALSE
  /\ participantVote = [ p \in participants |-> yes ]
  /\ participantAlive = [ p \in participants |-> TRUE ]
  /\ participantDecision = [ p \in participants |-> undecided ]
  /\ participantFaulty = [ p \in participants |-> FALSE ]
  /\ participantSent = [ p \in participants |-> FALSE ]

\* Coordinator actions
SendVoteRequest(p) ==
  /\ coordinatorAlive
  /\ coordinatorRequested[p] = FALSE
  /\ coordinatorRequested' = [ coordinatorRequested EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << coordinatorVote, coordinatorSent, coordinatorDecision,
                 coordinatorAlive, coordinatorFaulty, participantVote,
                 participantAlive, participantDecision, participantFaulty,
                 participantSent >>

ReceiveVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ AllVoteRequestsSent
  /\ coordinatorVote[p] = waiting
  /\ participantSent[p]
  /\ coordinatorVote' = [ coordinatorVote EXCEPT ![p] = participantVote[p] ]
  /\ UNCHANGED << coordinatorRequested, coordinatorSent, coordinatorDecision,
                 coordinatorAlive, coordinatorFaulty, participantVote,
                 participantAlive, participantDecision, participantFaulty,
                 participantSent >>

\* Failure detection is magical (not timeout): the coordinator notices a
\* participant that crashed without sending its vote, and decides to abort.
DetectParticipantFault(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ AllVoteRequestsSent
  /\ coordinatorVote[p] = waiting
  /\ participantAlive[p] = FALSE
  /\ coordinatorDecision' = abort
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorAlive, coordinatorFaulty, participantVote,
                 participantAlive, participantDecision, participantFaulty,
                 participantSent >>

MakeDecision ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ AllVotesReceived
  /\ coordinatorDecision' = (IF (\A p \in participants : coordinatorVote[p] = yes)
                              THEN commit ELSE abort)
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorAlive, coordinatorFaulty, participantVote,
                 participantAlive, participantDecision, participantFaulty,
                 participantSent >>

BroadcastDecision(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision # undecided
  /\ coordinatorSent[p] = notsent
  /\ coordinatorSent' = [ coordinatorSent EXCEPT ![p] = coordinatorDecision ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorDecision,
                 coordinatorAlive, coordinatorFaulty, participantVote,
                 participantAlive, participantDecision, participantFaulty,
                 participantSent >>

DieCoordinator ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, participantVote, participantAlive,
                 participantDecision, participantFaulty, participantSent >>

\* Participant actions
SendVote(p) ==
  /\ participantAlive[p]
  /\ participantSent[p] = FALSE
  /\ coordinatorRequested[p] = TRUE
  /\ participantSent' = [ participantSent EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 participantVote, participantAlive, participantDecision,
                 participantFaulty >>

AbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSent[p] = TRUE
  /\ participantVote[p] = no
  /\ participantDecision' = [ participantDecision EXCEPT ![p] = abort ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 participantVote, participantAlive, participantFaulty,
                 participantSent >>

AbortOnTimeoutNoRequest(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordinatorAlive = FALSE
  /\ coordinatorRequested[p] = FALSE
  /\ participantDecision' = [ participantDecision EXCEPT ![p] = abort ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 participantVote, participantAlive, participantFaulty,
                 participantSent >>

DecideOnCoordinatorBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordinatorSent[p] # notsent
  /\ participantDecision' = [ participantDecision EXCEPT ![p] = coordinatorSent[p] ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 participantVote, participantAlive, participantFaulty,
                 participantSent >>

DieParticipant(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [ participantAlive EXCEPT ![p] = FALSE ]
  /\ participantFaulty' = [ participantFaulty EXCEPT ![p] = TRUE ]
  /\ UNCHANGED << coordinatorRequested, coordinatorVote, coordinatorSent,
                 coordinatorDecision, coordinatorAlive, coordinatorFaulty,
                 participantVote, participantDecision, participantSent >>

CoordinatorProgress ==
  \/ ReceiveVote(\in participants) \/ DetectParticipantFault(\in participants)
  \/ BroadcastDecision(\in participants)
  \/ MakeDecision

ParticipantProgress ==
  \/ SendVote(\in participants) \/ AbortOnVote(\in participants)
  \/ AbortOnTimeoutNoRequest(\in participants) \/ DieParticipant(\in participants)
  \/ DecideOnCoordinatorBroadcast(\in participants)

Next ==
  \/ ParticipantProgress
  \/ CoordinatorProgress
  \/ DieCoordinator

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorProgress) /\ WF_vars(ParticipantProgress)

\* SAFETY: no two participants ever decide differently.
Agreement ==
  \A p, q \in participants :
    ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

\* Every commit must be backed by unanimity.
CommitValidity ==
  \A p \in participants :
    participantDecision[p] = commit => (\A q \in participants : participantVote[q] = yes)

\* Every abort is justified by a no vote, a faulty participant, or a faulty coordinator.
AbortValidity ==
  \A p \in participants :
    participantDecision[p] = abort =>
      (\E q \in participants : participantVote[q] = no \/ participantFaulty[q] = TRUE)
         \/ coordinatorFaulty = TRUE

\* Irreversibility: once decided, never changes again.
Irrevocability ==
  \A p \in participants :
    /\ (participantDecision[p] = commit => participantDecision' = [ participantDecision EXCEPT ![p] = commit ])
    /\ (participantDecision[p] = abort => participantDecision' = [ participantDecision EXCEPT ![p] = abort ])

\* LIVENESS: because broadcast is simple, we only guarantee that the system
\* either fully decides OR some fault is exposed (blocking can happen).
DecideOrExposeFault ==
  <>(\E p \in participants : participantDecision[p] # undecided)
      \/ (\E p \in participants : participantFaulty[p] = TRUE) \/ coordinatorFaulty = TRUE

====