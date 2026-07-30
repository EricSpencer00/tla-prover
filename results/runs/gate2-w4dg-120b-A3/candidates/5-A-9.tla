---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participantVote, participantAlive, participantDecision, participantFaulty,
         participantSentVote, coordSent, coordVotes, coordSentDecision,
         coordDecision, coordAlive, coordFaulty

vars == << participantVote, participantAlive, participantDecision,
           participantFaulty, participantSentVote, coordSent, coordVotes,
           coordSentDecision, coordDecision, coordAlive, coordFaulty >>

TypeOK ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive \in [participants -> BOOLEAN]
  /\ participantDecision \in [participants -> {undecided, commit, abort}]
  /\ participantFaulty \in [participants -> BOOLEAN]
  /\ participantSentVote \in [participants -> BOOLEAN]
  /\ coordSent \in [participants -> BOOLEAN]
  /\ coordVotes \in [participants -> {yes, no, waiting}]
  /\ coordSentDecision \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ participantVote \in [participants -> {yes, no}]
  /\ participantAlive = [p \in participants |-> TRUE]
  /\ participantDecision = [p \in participants |-> undecided]
  /\ participantFaulty = [p \in participants |-> FALSE]
  /\ participantSentVote = [p \in participants |-> FALSE]
  /\ coordSent = [p \in participants |-> FALSE]
  /\ coordVotes = [p \in participants |-> waiting]
  /\ coordSentDecision = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

SendVoteRequest(p) ==
  /\ coordAlive
  /\ ~coordSent[p]
  /\ coordSent' = [coordSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordVotes,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty >>

RecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p]
  /\ coordVotes[p] = waiting
  /\ participantSentVote[p]
  /\ coordVotes' = [coordVotes EXCEPT ![p] = participantVote[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordSent,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty >>

DetectCoordFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ coordSent[p]
  /\ coordVotes[p] = waiting
  /\ ~participantAlive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordSent,
                 coordVotes, coordSentDecision, coordAlive, coordFaulty >>

MakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants: coordVotes[p] # waiting
  /\ coordDecision' = IF (\A p \in participants: coordVotes[p] = yes) THEN commit ELSE abort
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordSent,
                 coordVotes, coordSentDecision, coordAlive, coordFaulty >>

BroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ coordSentDecision[p] = notsent
  /\ coordSentDecision' = [coordSentDecision EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordSent,
                 coordVotes, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, participantSentVote, coordSent,
                 coordVotes, coordSentDecision, coordDecision, coordAlive, coordFaulty >>

SendVote(p) ==
  /\ participantAlive[p]
  /\ coordSent[p]
  /\ ~participantSentVote[p]
  /\ participantSentVote' = [participantSentVote EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantAlive, participantDecision,
                 participantFaulty, coordSent, coordVotes, coordSentDecision,
                 coordDecision, coordAlive, coordFaulty >>

AbortOnVote(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ participantSentVote[p]
  /\ participantVote[p] = no
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSentVote, coordSent, coordVotes,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty >>

AbortOnTimeout(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ ~coordAlive
  /\ ~coordSent[p]
  /\ participantDecision' = [participantDecision EXCEPT ![p] = abort]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSentVote, coordSent, coordVotes,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty >>

DecideOnBroadcast(p) ==
  /\ participantAlive[p]
  /\ participantDecision[p] = undecided
  /\ coordSentDecision[p] # notsent
  /\ participantDecision' = [participantDecision EXCEPT ![p] = coordSentDecision[p]]
  /\ UNCHANGED << participantVote, participantAlive, participantFaulty,
                 participantSentVote, coordSent, coordVotes,
                 coordSentDecision, coordDecision, coordAlive, coordFaulty >>

ParticipantDie(p) ==
  /\ participantAlive[p]
  /\ participantAlive' = [participantAlive EXCEPT ![p] = FALSE]
  /\ participantFaulty' = [participantFaulty EXCEPT ![p] = TRUE]
  /\ UNCHANGED << participantVote, participantDecision, participantSentVote,
                 coordSent, coordVotes, coordSentDecision, coordDecision,
                 coordAlive, coordFaulty >>

CoordProgress ==
  \/ SendVoteRequest(anyP) \/ RecvVote(anyP) \/ DetectCoordFault(anyP)
  \/ MakeDecision \/ BroadcastDecision(anyP) \/ CoordDie

ParticipantProgress ==
  \/ SendVote(anyP) \/ AbortOnVote(anyP) \/ AbortOnTimeout(anyP) \/ DecideOnBroadcast(anyP) \/ ParticipantDie(anyP)

Next ==
  \/ CoordProgress
  \/ ParticipantProgress

Spec == Init /\ [][Next]_vars
        /\ WF_vars(DecideOnBroadcast(anyP))
        /\ WF_vars(CoordProgress)
        /\ WF_vars(ParticipantProgress)

anyP == CHOOSE p \in participants : TRUE

Agreement ==
  \A p1, p2 \in participants:
    (participantDecision[p1] = commit /\ participantDecision[p2] = abort) => FALSE

CommitValidity ==
  \A p \in participants: participantDecision[p] = commit => \A q \in participants: participantVote[q] = yes

AbortValidity ==
  \E p \in participants: participantDecision[p] = abort =>
    (\E q \in participants: participantVote[q] = no) \/ (\E q \in participants: participantFaulty[q]) \/ coordFaulty

Irrevocability ==
  \A p \in participants:
    /\ (participantDecision[p] = commit => (participantDecision' = [participantDecision EXCEPT ![p] = commit]))
    /\ (participantDecision[p] = abort => (participantDecision' = [participantDecision EXCEPT ![p] = abort]))

AllDecisionOrFault ==
  <>(\A p \in participants: participantDecision[p] # undecided) \/ (\E p \in participants: participantFaulty[p]) \/ coordFaulty

====