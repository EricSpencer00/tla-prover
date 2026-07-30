---- MODULE ACP_SB ----
EXTENDS Integers, FiniteSets

CONSTANTS
  participants,
  yes, no,
  undecided, commit, abort,
  waiting,
  notsent

VARIABLES
  participant,
  coordinator

TypeInvParticipant ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in [
    request   : [participants -> BOOLEAN],
    vote      : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}],
    decision  : {undecided, commit, abort},
    alive     : BOOLEAN,
    faulty    : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
  participant \in [
    participants -> [
      vote     |-> yes,
      alive    |-> TRUE,
      decision |-> undecided,
      faulty   |-> FALSE,
      voteSent |-> FALSE
    ]
  ]

InitCoordinator ==
  coordinator \in [
    request   |-> [p \in participants |-> FALSE],
    vote      |-> [p \in participants |-> waiting],
    broadcast |-> [p \in participants |-> notsent],
    decision  |-> undecided,
    alive     |-> TRUE,
    faulty    |-> FALSE
  ]

Init == InitParticipant /\ InitCoordinator

\* The coordinator sends a request for votes to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED participant

\* The coordinator records the vote of participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED participant

\* Failure is detected immediately: participant i died without sending a vote
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* The coordinator decides, once every participant has voted
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Simple broadcast: the coordinator sends its decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

\* A participant sends its vote to the coordinator
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED coordinator

\* A participant decides abort unilaterally upon voting no
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* A participant decides abort when the coordinator is dead and no request was sent
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* A participant adopts the coordinator's decision
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN   == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB    == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN    == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Death is not assumed weakly fair
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY

\* No two participants decide different outcomes
AC1 == [] \A i, j \in participants :
         \/ participant[i].decision # commit
         \/ participant[j].decision # abort

\* Commit only if every participant voted yes
AC2 == [] (\E i \in participants : participant[i].decision = commit) => \A j \in participants : participant[j].vote = yes

\* Abort only if some participant voted no or is faulty or the coordinator failed
AC3_1 == [] (\E i \in participants : participant[i].decision = abort) =>
            \/ \E j \in participants : participant[j].vote = no
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

\* Each participant decides at most once
AC4 ==
  [] /\ (\A i \in participants : participant[i].decision = commit => [] (participant[i].decision = commit))
     /\ (\A i \in participants : participant[i].decision = abort  => [] (participant[i].decision = abort))

\* LIVENESS: somebody eventually decides, or some component fails

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

====