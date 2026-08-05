---- MODULE ACP_SB ----
EXTENDS Naturals

\* Atomic Commitment Protocol with Simple Broadcast (ACP-SB), following Babaoglu and
\* Toueg. One coordinator collects votes from participants, decides commit or
\* abort, and broadcasts the decision one participant at a time (simple
\* broadcast). Any actor may die silently, which can leave an undecided
\* participant behind -- this is a blocking protocol, not a non-blocking one.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES coordinatorVote, coordinatorDecision, coordinatorAlive,
          participantVote, participantDecision, participantAlive,
          coordinatorRequest, coordinatorReply, coordinatorSend, participantSent

vars == <<coordinatorVote, coordinatorDecision, coordinatorAlive,
          participantVote, participantDecision, participantAlive,
          coordinatorRequest, coordinatorReply, coordinatorSend, participantSent>>

Init ==
  /\ coordinatorVote = [p \in participants |-> waiting]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = TRUE
  /\ participantVote = [p \in participants |-> yes]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ coordinatorRequest = [p \in participants |-> FALSE]
  /\ coordinatorReply = [p \in participants |-> waiting]
  /\ coordinatorSend = [p \in participants |-> notsent]
  /\ participantSent = [p \in participants |-> FALSE]

\* The coordinator asks a participant to vote.
CoordinatorRequestVote(p) ==
  /\ coordinatorAlive
  /\ ~coordinatorRequest[p]
  /\ coordinatorRequest' = [coordinatorRequest EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordinatorVote, coordinatorDecision, coordinatorAlive,
                 participantVote, participantDecision, participantAlive,
                 coordinatorReply, coordinatorSend, participantSent>>

\* The coordinator receives a participant's vote (the participant already sent it).
CoordinatorReceiveVote(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A q \in participants : coordinatorRequest[q]
  /\ coordinatorReply[p] = waiting
  /\ participantSent[p]
  /\ coordinatorVote' = [coordinatorVote EXCEPT ![p] = participantVote[p]]
  /\ coordinatorReply' = [coordinatorReply EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED <<coordinatorDecision, coordinatorAlive,
                 participantVote, participantDecision, participantAlive,
                 coordinatorRequest, coordinatorSend, participantSent>>

\* The coordinator detects a participant fault (waited on a dead participant).
CoordinatorDetectParticipantFault(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ coordinatorRequest[p]
  /\ coordinatorReply[p] = waiting
  /\ ~participantAlive[p]
  /\ coordinatorDecision' = abort
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorRequest,
                 coordinatorSend, participantVote, participantDecision,
                 participantAlive, coordinatorAlive, participantSent>>

\* The coordinator makes its decision after collecting all votes.
CoordinatorMakeDecision ==
  /\ coordinatorAlive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants : coordinatorRequest[p]
  /\ \A p \in participants : coordinatorReply[p] # waiting
  /\ coordinatorDecision' =
       IF \A p \in participants : coordinatorVote[p] = yes
       THEN commit
       ELSE abort
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorRequest,
                 coordinatorSend, participantVote, participantDecision,
                 participantAlive, coordinatorAlive, participantSent>>

\* Simple broadcast: the coordinator sends its decision to one participant at a time.
CoordinatorBroadcast(p) ==
  /\ coordinatorAlive
  /\ coordinatorDecision # undecided
  /\ coordinatorSend[p] = notsent
  /\ coordinatorSend' = [coordinatorSend EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED <<coordinatorVote, coordinatorDecision, coordinatorRequest,
                 coordinatorReply, participantVote, participantDecision,
                 participantAlive, participantSent, coordinatorAlive>>

\* The coordinator dies (silent failure).
CoordinatorDie ==
  /\ coordinatorAlive
  /\ coordinatorAlive' = FALSE
  /\ UNCHANGED <<coordinatorVote, coordinatorDecision, coordinatorRequest,
                 coordinatorReply, participantVote, participantDecision,
                 participantAlive, coordinatorSend, participantSent>>

\* A participant sends its vote to the coordinator.
ParticipantSendVote(p) ==
  /\ participantAlive[p]
  /\ coordinatorRequest[p]
  /\ ~participantSent[p]
  /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorDecision,
                 coordinatorAlive, participantVote, participantDecision,
                 participantAlive, coordinatorRequest, coordinatorSend>>

\* A participant aborts on its own vote being no.
ParticipantAbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSent[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorDecision,
                 coordinatorAlive, participantVote, participantAlive,
                 coordinatorRequest, coordinatorSend, participantSent>>

\* A participant times out on a missing vote request (coordinator died).
ParticipantAbortOnTimeout(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordinatorAlive
  /\ ~coordinatorRequest[p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorDecision,
                 coordinatorAlive, participantVote, participantAlive,
                 coordinatorRequest, coordinatorSend, participantSent>>

\* A participant adopts the coordinator's broadcast decision.
ParticipantDecideOnBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordinatorSend[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordinatorSend[p]]
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorDecision,
                 coordinatorAlive, participantVote, participantAlive,
                 coordinatorRequest, coordinatorSend, participantSent>>

\* A participant dies (silent failure).
ParticipantDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<coordinatorVote, coordinatorReply, coordinatorDecision,
                 coordinatorAlive, participantVote, participantDecision,
                 coordinatorRequest, coordinatorSend, participantSent>>

CoordinatorProgress ==
  \/ \E p \in participants : CoordinatorRequestVote(p)
  \/ \E p \in participants : CoordinatorReceiveVote(p)
  \/ \E p \in participants : CoordinatorDetectParticipantFault(p)
  \/ CoordinatorMakeDecision
  \/ \E p \in participants : CoordinatorBroadcast(p)

ParticipantProgress(p) ==
  \/ ParticipantSendVote(p)
  \/ ParticipantAbortOnVote(p)
  \/ ParticipantAbortOnTimeout(p)
  \/ ParticipantDecideOnBroadcast(p)

Next ==
  \/ CoordinatorProgress
  \/ CoordinatorDie
  \/ \E p \in participants : ParticipantProgress(p)
  \/ \E p \in participants : ParticipantDie(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordinatorDie)
             /\ \A p \in participants : WF_vars(ParticipantDie(p))

\* AC1: No two participants decide differently -- commit and abort are mutually
\* exclusive across the whole group.
AC1 == ~( (\E x \in participants : participantDecision[x] = commit)
           /\ (\E y \in participants : participantDecision[y] = abort) )

\* AC2: A commit is only possible if every participant voted yes.
AC2 == \A p \in participants : participantDecision[p] = commit => \A q \in participants : participantVote[q] = yes

\* AC3: An abort requires a vote-no or a crash of some participant or the
\* coordinator -- never an unexplained abort.
AC3 == \A p \in participants : participantDecision[p] = abort =>
        ( \E q \in participants : participantVote[q] = no
          \/ \E q \in participants : ~participantAlive[q]
          \/ ~coordinatorAlive )

\* AC4: A participant decides at most once -- its decision never flips.
AC4 == \A p \in participants : (participantDecision[p] = commit => participantDecision[p] = commit)
                                /\ (participantDecision[p] = abort => participantDecision[p] = abort)

\* AC3 liveness component (the blocking termination condition): either every
\* participant eventually decides, or some participant or the coordinator is
\* eventually found faulty.
AC3Component ==
  /\ (\A p \in participants : participantDecision[p] # undecided)
       \/ (\E p \in participants : ~participantAlive[p])
       \/ ~coordinatorAlive

varsType ==
  /\ coordinatorVote \in [participants -> {yes, no, waiting}]
  /\ coordinatorDecision \in {undecided, commit, abort}
  /\ coordinatorAlive \in BOOLEAN
  /\ coordinatorRequest \in [participants -> BOOLEAN]
  /\ coordinatorReply \in [participants -> {yes, no, waiting}]
  /\ coordinatorSend \in [participants -> {commit, abort, notsent}]
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantSent \in [participants -> BOOLEAN]

TypeInv == varsType

Liveness == \A p \in participants : WF_vars(ParticipantProgress(p))
            /\ \A p \in participants : SF_vars(ParticipantProgress(p))
            /\ AC3Component

====