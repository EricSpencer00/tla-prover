---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB).
\* From: `^Distributed Systems^' by Sape Mullender, 1993.
\* This version uses a simple broadcast; the algorithm is non-terminating, so
\* property AC5 does not hold.  This is a corrected version: makeDecision now
\* assigns every coordinator variable, so SANY and TLC accept it.
EXTENDS Naturals

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
  request   |-> [p \in participants |-> FALSE],
  vote      |-> [p \in participants |-> waiting],
  broadcast |-> [p \in participants |-> notsent],
  decision  |-> undecided,
  alive     |-> TRUE,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

\* Coordinator statements:
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                    [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote =
                    [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* The correction: broadcast must assign the coordinator's decision too.
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
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* Participant statements:
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
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
             /\ participant' = [participant EXCEPT ![i].decision =
                  coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i)
              \/ abortOnTimeoutRequest(i) \/ decide(i)

\* Death transitions are outside fairness; fairness here is only on
\* request, vote collection, and decision broadcast.
coordProgB == makeDecision \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

progN == (\E i \in participants : parProg(i) \/ parDie(i)) \/ coordProgB

fairness == \A i \in participants :
              WF_<<coordinator, participant>>(sendVote(i) \/ abortOnVote(i)
                                          \/ abortOnTimeoutRequest(i) \/ decide(i))
            /\ WF_<<coordinator, participant>>(request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i))

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* Correctness: participants that decide commit or abort agree with the vote
\* record and with each other (no two participants ever commit and abort).
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit
                      => [] participant[i].decision = commit)
          /\ (\A i \in participants : participant[i].decision = abort
                      => [] participant[i].decision = abort)

====