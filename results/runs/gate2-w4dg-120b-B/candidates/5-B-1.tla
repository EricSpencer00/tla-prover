---- MODULE W4DG120b5m9p0t0 ----
EXTENDS Naturals, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : BOOLEAN,
    decision : {undecided, commit, abort},
    faulty   : BOOLEAN,
    voteSent : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in [
  request   : [participants -> BOOLEAN],
  vote      : [participants -> {waiting, yes, no}],
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {commit, abort, undecided},
  alive     : BOOLEAN,
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [
  participants -> [
    vote     |-> yes,
    alive    |-> TRUE,
    decision |-> undecided,
    faulty   |-> FALSE,
    voteSent |-> FALSE
  ]
]

InitCoordinator == coordinator \in [
  request   |-> [participants |-> FALSE],
  vote      |-> [participants |-> waiting],
  broadcast|-> [participants |-> notsent],
  decision  |-> undecided,
  alive     |-> TRUE,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
              /\ UNCHANGED participant

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
              /\ UNCHANGED participant

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED participant

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, !.faulty = TRUE]
             /\ UNCHANGED coordinator

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
coordProg(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

prog == \E i \in participants : parProg(i) \/ coordProg(i) \/ coordDie

Spec == Init /\ [][prog]_<<coordinator, participant>>

\* Safety: all participants that decide agree, and commit requires all votes yes.
\* Stronger than the paper: abort must be backed by a no vote or a failure.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)

AC3 == [] (\E i \in participants : participant[i].decision = abort)
           => \/ \E j \in participants : participant[j].vote = no
              \/ \E j \in participants : participant[j].faulty
              \/ coordinator.faulty

\* Each participant decides at most once.
AC4 == [] (\A i \in participants :
             participant[i].decision = commit => [](participant[i].decision = commit))
           /\ (\A i \in participants :
               participant[i].decision = abort => [](participant[i].decision = abort))

\* Non-terminating: the broadcast may keep being interrupted.
AC5 == <> \A i \in participants :
           \/ participant[i].decision \in {abort, commit}
           \/ participant[i].faulty

====