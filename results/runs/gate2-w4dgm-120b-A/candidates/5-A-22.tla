---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* Coordinator and participants both collect votes and decide; a crash may leave
\* some participants without a decision (hence "blocking" in the simple broadcast variant).
VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
          participantSent, coordRequested, coordVote, coordSent, coordDecision,
          coordAlive, coordFaulty

vars == <<participantVote, participantAlive, participantDecision, participantFaulty,
           participantSent, coordRequested, coordVote, coordSent, coordDecision,
           coordAlive, coordFaulty>>

TypeOK ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSent \in [participants -> BOOLEAN]
  /\ coordRequested \in [participants -> BOOLEAN]
  /\ coordVote \in [participants -> {yes, no, waiting}]
  /\ coordSent \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSent = [p \in participants |-> FALSE]
  /\ coordRequested = [p \in participants |-> FALSE]
  /\ coordVote = [p \in participants |-> waiting]
  /\ coordSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

\* Coordinator (co-) actions.
SendVoteReq(p) ==
  /\ coordAlive
  /\ ~coordRequested[p]
  /\ coordRequested' = [coordRequested EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordVote, coordSent,
                 coordDecision, coordFaulty>>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ participantSent[p]
  /\ coordVote' = [coordVote EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordRequested, coordSent,
                 coordDecision, coordAlive, coordFaulty>>

DetectParticipantFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordRequested[p]
  /\ coordVote[p] = waiting
  /\ ~participantAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordRequested, coordVote,
                 coordSent, coordAlive, coordFaulty>>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : coordVote[p] # waiting
  /\ coordDecision' = (IF \A p \in participants : coordVote[p] = yes THEN commit ELSE abort)
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSent, coordRequested, coordVote, coordSent, coordAlive, coordFaulty>>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision \in {commit, abort}
  /\ coordSent[p] = notsent
  /\ coordSent' = [coordSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSent, coordRequested, coordVote,
                 coordDecision, coordAlive, coordFaulty>>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 participantSent, coordRequested, coordVote, coordSent, coordDecision>>

\* Participant (pt-) actions.
SendVote(p) ==
  /\ participantAlive[p]
  /\ coordRequested[p]
  /\ ~participantSent[p]
  /\ participantSent' = [participantSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantAlive, participantDecision, participantFaulty,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSent[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty, participantSent,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

AbortOnReqTimeout(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordRequested[p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty, participantSent,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

DecideOnBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordSent[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordSent[p]]
  /\ UNCHANGED <<participantVote, participantAlive, participantFaulty, participantSent,
                 coordRequested, coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

PartDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<participantVote, participantDecision, participantSent, coordRequested,
                 coordVote, coordSent, coordDecision, coordAlive, coordFaulty>>

Next ==
  \/ \E p \in participants : SendVoteReq(p) \/ RecvVote(p) \/ DetectParticipantFault(p)
                              \/ BroadcastDecision(p) \/ SendVote(p) \/ AbortOnVote(p)
                              \/ AbortOnReqTimeout(p) \/ DecideOnBroadcast(p) \/ PartDie(p)
  \/ MakeDecision
  \/ CoordDie

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in participants : SendVote(p))
  /\ WF_vars(\E p \in participants : AbortOnVote(p))
  /\ WF_vars(\E p \in participants : DecideOnBroadcast(p))
  /\ WF_vars(\E p \in participants : SendVoteReq(p))
  /\ WF_vars(\E p \in participants : RecvVote(p))
  /\ WF_vars(\E p \in participants : BroadcastDecision(p))

\* SAFETY: no two participants end up in contradictory final states.
Agreement ==
  \A p, q \in participants :
    ~(participantDecision[p] = commit /\ participantDecision[q] = abort)

CommitValid ==
  \A p \in participants : participantDecision[p] = commit => \A q \in participants : participantVote[q] = yes

AbortValid ==
  \A p \in participants : participantDecision[p] = abort =>
    \E q \in participants : participantVote[q] = no \/ participantFaulty[q] \/ coordFaulty

DecidedOnce == \A p \in participants :
  (participantDecision[p] = commit) ~> (participantDecision[p] = commit)

\* LIVENESS: eventually everyone decides, or some node is found faulty.
DecisionEventually ==
  <>(\A p \in participants : participantDecision[p] # undecided \/ \E p \in participants : participantFaulty[p] \/ coordFaulty)

Properties == Agreement /\ CommitValid /\ AbortValid /\ DecidedOnce

Terminating == Spec /\ DecidedOnce

====