---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES
  vote, alive, decision, faulty, sentVote,
  reqSent, recvVote, broadcastSent, coordDecision, coordAlive, coordFaulty

vars == << vote, alive, decision, faulty, sentVote,
            reqSent, recvVote, broadcastSent, coordDecision, coordAlive, coordFaulty >>

TypeInv ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive \in [participants -> BOOLEAN]
  /\ decision \in [participants -> {undecided, commit, abort}]
  /\ faulty \subseteq participants
  /\ sentVote \subseteq participants
  /\ reqSent \in [participants -> BOOLEAN]
  /\ recvVote \in [participants -> {yes, no, waiting}]
  /\ broadcastSent \in [participants -> {commit, abort, notsent}]
  /\ coordDecision \in {undecided, commit, abort}
  /\ coordAlive \in BOOLEAN
  /\ coordFaulty \in BOOLEAN

Init ==
  /\ vote \in [participants -> {yes, no}]
  /\ alive = [p \in participants |-> TRUE]
  /\ decision = [p \in participants |-> undecided]
  /\ faulty = {}
  /\ sentVote = {}
  /\ reqSent = [p \in participants |-> FALSE]
  /\ recvVote = [p \in participants |-> waiting]
  /\ broadcastSent = [p \in participants |-> notsent]
  /\ coordDecision = undecided
  /\ coordAlive = TRUE
  /\ coordFaulty = FALSE

CoordSendVoteReq(p) ==
  /\ coordAlive
  /\ ~reqSent[p]
  /\ reqSent' = [reqSent EXCEPT ![p] = TRUE]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 recvVote, broadcastSent, coordDecision, coordAlive, coordFaulty >>

CoordRecvVote(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ p \in sentVote
  /\ recvVote' = [recvVote EXCEPT ![p] = vote[p]]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, broadcastSent, coordDecision, coordAlive, coordFaulty >>

CoordDetectFault(p) ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ reqSent[p]
  /\ recvVote[p] = waiting
  /\ ~alive[p]
  /\ coordDecision' = abort
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recvVote, broadcastSent, coordAlive, coordFaulty >>

CoordMakeDecision ==
  /\ coordAlive
  /\ coordDecision = undecided
  /\ \A p \in participants : recvVote[p] # waiting
  /\ coordDecision' = IF \A p \in participants : recvVote[p] = yes THEN commit ELSE abort
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recvVote, broadcastSent, coordAlive, coordFaulty >>

CoordBroadcastDecision(p) ==
  /\ coordAlive
  /\ coordDecision # undecided
  /\ broadcastSent[p] = notsent
  /\ broadcastSent' = [broadcastSent EXCEPT ![p] = coordDecision]
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recvVote, coordDecision, coordAlive, coordFaulty >>

CoordDie ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ coordFaulty' = TRUE
  /\ UNCHANGED << vote, alive, decision, faulty, sentVote,
                 reqSent, recvVote, broadcastSent, coordDecision, coordFaulty >>

ParticipantSendVote(p) ==
  /\ alive[p]
  /\ reqSent[p]
  /\ p \notin sentVote
  /\ sentVote' = sentVote \cup {p}
  /\ UNCHANGED << vote, alive, decision, faulty, reqSent,
                 recvVote, broadcastSent, coordDecision, coordAlive, coordFaulty >>

ParticipantAbortOnVote(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ p \in sentVote
  /\ vote[p] = no
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty,
                 sentVote, reqSent, recvVote, broadcastSent,
                 coordDecision, coordAlive, coordFaulty >>

ParticipantAbortTimeout(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ ~coordAlive
  /\ reqSent[p] = FALSE
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ UNCHANGED << vote, alive, faulty,
                 sentVote, reqSent, recvVote, broadcastSent,
                 coordDecision, coordAlive, coordFaulty >>

ParticipantDecide(p) ==
  /\ alive[p]
  /\ decision[p] = undecided
  /\ broadcastSent[p] # notsent
  /\ decision' = [decision EXCEPT ![p] = broadcastSent[p]]
  /\ UNCHANGED << vote, alive, faulty,
                 sentVote, reqSent, recvVote, broadcastSent,
                 coordDecision, coordAlive, coordFaulty >>

ParticipantDie(p) ==
  /\ alive[p]
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ decision' = [decision EXCEPT ![p] = abort]
  /\ faulty' = faulty \cup {p}
  /\ UNCHANGED << vote, sentVote, reqSent,
                 recvVote, broadcastSent, coordDecision, coordAlive, coordFaulty >>

Next ==
  \/ \E p \in participants :
       \/ CoordSendVoteReq(p) \/ CoordRecvVote(p) \/ CoordDetectFault(p)
       \/ CoordBroadcastDecision(p)
       \/ ParticipantSendVote(p) \/ ParticipantAbortOnVote(p)
       \/ ParticipantAbortTimeout(p) \/ ParticipantDecide(p)
       \/ ParticipantDie(p)
  \/ CoordMakeDecision \/ CoordDie

CoordProgress ==
  \/ CoordMakeDecision
  \/ \E p \in participants : CoordBroadcastDecision(p)
  \/ \E p \in participants : CoordDetectFault(p)

ParticipantProgress ==
  \/ \E p \in participants : ParticipantSendVote(p) \/ ParticipantAbortOnVote(p)
  \/ \E p \in participants : ParticipantAbortTimeout(p) \/ ParticipantDecide(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProgress) /\ WF_vars(ParticipantProgress)

AllDecided == \A p \in participants : decision[p] # undecided

AC1 == \A p \in participants : decision[p] = commit => \A q \in participants : decision[q] = commit

AC2 == (\E p \in participants : decision[p] = commit) => \A p \in participants : vote[p] = yes

AC3 == (\E p \in participants : decision[p] = abort) =>
         ( \E p \in participants : vote[p] = no \/ p \in faulty \/ coordFaulty )

AC4 == \A p \in participants :
         (decision[p] = commit) ~> (decision[p] = commit) /\ (decision[p] = abort) ~> (decision[p] = abort)

AC3Live == <> (AllDecided \/ coordFaulty \/ faulty # {})

====