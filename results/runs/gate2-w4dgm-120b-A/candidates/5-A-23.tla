---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

Alive == "alive"
Dead == "dead"

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
          coordinatorDecision, coordinatorAlive, coordinatorFaulty

vars == << participantVote, participantAlive, participantDecision, participantFaulty,
           participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
           coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

TypeInv ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> {Alive, Dead}]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSent \in [participants -> BOOLEAN]
  /\ coordinatorAsked \in [participants -> BOOLEAN]
  /\ coordinatorVote \in [participants -> {yes, no, waiting}]
  /\ coordinatorBroadcast \in [participants -> {commit, abort, notsent}]
  /\ coordinatorDecision \in {commit, abort, undecided}
  /\ coordinatorAlive \in {Alive, Dead}
  /\ coordinatorFaulty \in BOOLEAN

Init ==
  /\ \E p \in participants : participantVote = [q \in participants |-> p]
  /\ participantAlive = [p \in participants |-> Alive]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSent = [p \in participants |-> FALSE]
  /\ coordinatorAsked = [p \in participants |-> FALSE]
  /\ coordinatorVote = [p \in participants |-> waiting]
  /\ coordinatorBroadcast = [p \in participants |-> notsent]
  /\ coordinatorDecision = undecided
  /\ coordinatorAlive = Alive
  /\ coordinatorFaulty = FALSE

SendVoteRequest(p) ==
  /\ coordinatorAlive = Alive
  /\ ~coordinatorAsked[p]
  /\ coordinatorAsked' = [coordinatorAsked EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ReceiveVote(p) ==
  /\ coordinatorAlive = Alive
  /\ coordinatorDecision = undecided
  /\ coordinatorAsked[p]
  /\ coordinatorVote[p] = waiting
  /\ participantSent[p]
  /\ coordinatorVote' = [coordinatorVote EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

DetectParticipantFault(p) ==
  /\ coordinatorAlive = Alive
  /\ coordinatorDecision = undecided
  /\ coordinatorAsked[p]
  /\ coordinatorVote[p] = waiting
  /\ participantAlive[p] = Dead
  /\ ~participantSent[p]
  /\ coordinatorDecision' = abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorAlive, coordinatorFaulty >>

MakeDecision ==
  /\ coordinatorAlive = Alive
  /\ coordinatorDecision = undecided
  /\ \A p \in participants : coordinatorVote[p] # waiting
  /\ coordinatorDecision' = IF \A p \in participants : coordinatorVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorAlive, coordinatorFaulty >>

BroadcastDecision(p) ==
  /\ coordinatorAlive = Alive
  /\ coordinatorDecision # undecided
  /\ coordinatorBroadcast[p] = notsent
  /\ coordinatorBroadcast' = [coordinatorBroadcast EXCEPT ![p] = coordinatorDecision]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

CoordinatorDie ==
  /\ coordinatorAlive = Alive
  /\ coordinatorAlive' = Dead
  /\ coordinatorFaulty' = TRUE
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorFaulty >>

SendVote(p) ==
  /\ participantAlive[p] = Alive
  /\ coordinatorAsked[p]
  /\ ~participantSent[p]
  /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision, participantFaulty,
                  coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

AbortOnVote(p) ==
  /\ participantAlive[p] = Alive
  /\ participantDecision[p] = undecided
  /\ participantSent[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

AbortOnTimeoutNoRequest(p) ==
  /\ participantAlive[p] = Alive
  /\ participantDecision[p] = undecided
  /\ coordinatorAlive = Dead
  /\ ~coordinatorAsked[p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

DecideFromCoordinator(p) ==
  /\ participantAlive[p] = Alive
  /\ participantDecision[p] = undecided
  /\ coordinatorBroadcast[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordinatorBroadcast[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                  participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                  coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

ParticipantDie(p) ==
  /\ participantAlive[p] = Alive
  /\ participantAlive' = [participantAlive EXCEPT ![p] = Dead]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantDecision, participantSent, coordinatorAsked,
                  coordinatorVote, coordinatorBroadcast, coordinatorDecision,
                  coordinatorAlive, coordinatorFaulty >>

Next ==
  \/ \E p \in participants :
       SendVoteRequest(p) \/ ReceiveVote(p) \/ DetectParticipantFault(p)
         \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
         \/ AbortOnTimeoutNoRequest(p) \/ DecideFromCoordinator(p)
         \/ ParticipantDie(p)
  \/ MakeDecision
  \/ CoordinatorDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in participants : WF_vars(SendVote(p))
  /\ \A p \in participants : WF_vars(DecideFromCoordinator(p))
  /\ \A p \in participants : WF_vars(AbortOnVote(p))

AC1NoDoubleAllocation ==
  \A p, q \in participants :
     (participantDecision[p] = commit /\ participantDecision[q] = abort) => p = q

AC2CommitImpliesAllYes ==
  (\E p \in participants : participantDecision[p] = commit)
    => \A q \in participants : participantVote[q] = yes

AC3AbortRequiresDisagree ==
  (\E p \in participants : participantDecision[p] = abort)
    => (\E q \in participants : participantVote[q] = no)
         \/ (\E q \in participants : participantFaulty[q])
         \/ coordinatorFaulty

AC4Irreversible ==
  \A p \in participants :
    /\ (participantDecision[p] = commit => participantDecision' = [participantDecision EXCEPT ![p] = commit])
    /\ (participantDecision[p] = abort => participantDecision' = [participantDecision EXCEPT ![p] = abort])
    /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                    participantSent, coordinatorAsked, coordinatorVote, coordinatorBroadcast,
                    coordinatorDecision, coordinatorAlive, coordinatorFaulty >>

AC3Liveness == <>(\A p \in participants : participantDecision[p] # undecided \/ coordinatorFaulty \/ \E q \in participants : participantFaulty[q])

====