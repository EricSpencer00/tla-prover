---- MODULE ACP_NB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* ACP-NB extends the simple broadcast ACP-SB with a reliable broadcast: a
\* participant forwards the received pre-decision to every other participant
\* before finalizing locally. This is what keeps termination live even if the
\* coordinator crashes mid-broadcast.
VARIABLES v, alive, decision, faulty, voteSent, pstate, coord, fwd

TypeOK ==
  /\ v \in [participants -> {yes, no, undecided}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ faulty \in [participants -> BOOLEAN]
  /\ voteSent \in [participants -> BOOLEAN]
  /\ pstate \in {"idle", "waiting", "voting"}
  /\ coord \in [request : BOOLEAN, vote : {yes, no, undecided},
                 bcast : BOOLEAN, decision : {commit, abort, waiting}, alive : BOOLEAN, faulty : BOOLEAN]
  /\ fwd \in [participants -> [participants -> {notsent, commit, abort}]]

Init ==
  /\ v = [p \in participants |-> undecided]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> waiting]
  /\ faulty = [p \in participants |-> FALSE]
  /\ voteSent = [p \in participants |-> FALSE]
  /\ pstate = "idle"
  /\ coord = [request |-> FALSE, vote |-> undecided, bcast |-> FALSE,
              decision |-> waiting, alive |-> TRUE, faulty |-> FALSE]
  /\ fwd = [p \in participants |-> [q \in participants |-> notsent]]

CoordinatorSendRequest ==
  /\ coord.alive
  /\ coord.request = FALSE
  /\ coord.vote = undecided
  /\ coord.bcast = FALSE
  /\ coord.decision = waiting
  /\ coord.request' = TRUE
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate, fwd>>

CoordinatorCollectVote ==
  /\ coord.request
  /\ coord.vote = undecided
  /\ \E p \in participants: alive[p] /\ voteSent[p]
  /\ coord.vote' = IF \E p \in participants: v[p] = no THEN no ELSE yes
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate, fwd>>

CoordinatorDetectFault ==
  /\ coord.alive
  /\ coord.request
  /\ coord.vote = undecided
  /\ \E p \in participants: ~alive[p]
  /\ coord.faulty' = TRUE
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate, fwd>>

CoordinatorMakeDecision ==
  /\ coord.request
  /\ coord.vote # undecided
  /\ coord.decision = waiting
  /\ coord.decision' = IF coord.vote = yes THEN commit ELSE abort
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate, fwd>>

CoordinatorBroadcast ==
  /\ coord.alive
  /\ coord.decision # waiting
  /\ coord.bcast = FALSE
  /\ \A p \in participants: alive[p] => fwd[p][p] = notsent
  /\ fwd' = [p \in participants |-> [q \in participants |->
                 IF alive[p] /\ alive[q] THEN IF q = p THEN commit ELSE decision[p]
                 ELSE fwd[p][q]]]
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate>>

CoordinatorDie ==
  /\ coord.alive
  /\ coord.alive' = FALSE
  /\ UNCHANGED <<coord, v, alive, decision, faulty, voteSent, pstate, fwd>>

ParticipantSendVote ==
  /\ pstate = "waiting"
  /\ \E vval \in {yes, no}: v' = [v EXCEPT ![pstate] = vval]
  /\ voteSent' = [voteSent EXCEPT ![pstate] = TRUE]
  /\ pstate' = "voting"
  /\ UNCHANGED <<alive, decision, faulty, coord, fwd>>

ParticipantAbortOnVote ==
  /\ pstate = "voting"
  /\ v[pstate] = no
  /\ decision' = [decision EXCEPT ![pstate] = abort]
  /\ UNCHANGED <<v, alive, faulty, voteSent, pstate, coord, fwd>>

ParticipantAbortOnTimeoutForRequest ==
  /\ pstate = "waiting"
  /\ coord.faulty
  /\ ~coord.alive
  /\ decision' = [decision EXCEPT ![pstate] = abort]
  /\ UNCHANGED <<v, alive, faulty, voteSent, pstate, coord, fwd>>

\* A participant stores a decision it has received from the coordinator.
ParticipantPredecideFromCoordinator ==
  /\ alive[pstate]
  /\ decision[pstate] = waiting
  /\ coord.bcast
  /\ coord.decision # waiting
  /\ fwd[pstate][pstate] = notsent
  /\ fwd' = [fwd EXCEPT ![pstate][pstate] = coord.decision]
  /\ UNCHANGED <<v, alive, decision, faulty, voteSent, pstate, coord>>

\* A participant stores a decision it has received from another participant.
ParticipantPredecideFromFwd ==
  /\ alive[pstate]
  /\ decision[pstate] = waiting
  /\ \E from \in participants: from # pstate /\ fwd[from][pstate] # notsent
  /\ fwd' = [fwd EXCEPT ![pstate][pstate] = CHOOSE from \in participants:
                 from # pstate /\ fwd[from][pstate] # notsent: fwd[from][pstate]]
  /\ UNCHANGED <<v, alive, decision, faulty, voteSent, pstate, coord>>

ParticipantForward ==
  /\ alive[pstate]
  /\ fwd[pstate][pstate] # notsent
  /\ \E q \in participants: alive[q] /\ fwd[pstate][q] = notsent
       /\ fwd' = [fwd EXCEPT ![pstate][q] = fwd[pstate][pstate]]
  /\ UNCHANGED <<v, alive, decision, faulty, voteSent, pstate, coord>>

ParticipantDecide ==
  /\ alive[pstate]
  /\ decision[pstate] = waiting
  /\ fwd[pstate][pstate] # notsent
  /\ \A q \in participants: alive[q] => fwd[pstate][q] # notsent
  /\ decision' = [decision EXCEPT ![pstate] = fwd[pstate][pstate]]
  /\ UNCHANGED <<v, alive, faulty, voteSent, pstate, coord, fwd>>

ParticipantAbortOnTimeoutForFwd ==
  /\ alive[pstate]
  /\ decision[pstate] = waiting
  /\ ~coord.alive
  /\ \A p \in participants: ~coord.bcast /\ v[p] = undecided
  /\ ~(\E from \in participants, to \in participants: ~alive[from] /\ fwd[from][to] # notsent)
  /\ decision' = [decision EXCEPT ![pstate] = abort]
  /\ UNCHANGED <<v, alive, faulty, voteSent, pstate, coord, fwd>>

ParticipantDie ==
  /\ alive[pstate]
  /\ alive' = [alive EXCEPT ![pstate] = FALSE]
  /\ pstate' = "idle"
  /\ UNCHANGED <<v, decision, faulty, voteSent, coord, fwd>>

\* Participant progress actions get weak fairness; death is excluded.
Next ==
  \/ CoordinatorSendRequest
  \/ CoordinatorCollectVote
  \/ CoordinatorDetectFault
  \/ CoordinatorMakeDecision
  \/ CoordinatorBroadcast
  \/ CoordinatorDie
  \/ ParticipantSendVote
  \/ ParticipantAbortOnVote
  \/ ParticipantAbortOnTimeoutForRequest
  \/ ParticipantPredecideFromCoordinator
  \/ ParticipantPredecideFromFwd
  \/ ParticipantForward
  \/ ParticipantDecide
  \/ ParticipantAbortOnTimeoutForFwd
  \/ ParticipantDie

SpecNB ==
  /\ Init
  /\ [][Next]_<<v, alive, decision, faulty, voteSent, pstate, coord, fwd>>
  /\ WF_vars(CoordinatorBroadcast)
  /\ \A p \in participants:
       /\ WF_vars(ParticipantPredecideFromCoordinator)
       /\ WF_vars(ParticipantPredecideFromFwd)
       /\ WF_vars(ParticipantForward)
       /\ WF_vars(ParticipantDecide)

TypeInvNB ==
  /\ TypeOK
  /\ decision \in [participants -> {commit, abort, waiting}]
  /\ coord.decision \in {commit, abort, waiting}
  /\ coord.request \in BOOLEAN
  /\ coord.bcast \in BOOLEAN

Agreement ==
  /\ \A p, q \in participants: (decision[p] = commit /\ decision[q] = abort) => FALSE
  /\ \A p \in participants: (decision[p] = commit) => (\A q \in participants: v[q] = yes)
  /\ \A p \in participants: (decision[p] = abort) =>
       (\E q \in participants: v[q] = no \/ faulty[q] \/ coord.faulty)

Termination ==
  \A p \in participants: (coord.faulty \/ decision[p] # waiting) ~> decision[p] # waiting

====