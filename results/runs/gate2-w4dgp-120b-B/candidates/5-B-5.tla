---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\*******************************************************************************
\* Synchronous communication has been replaced with (implicit) asynchronous communication.
\* Failures are detected "magically" instead or relying on timeouts.
\*
\* This version of the protocol uses a "simple broadcast" where a broadcast is simply a 
\* series of messages sent, possibly interrupted by a failure.  Consequently, this algorithm
\* is "non terminating" and property AC5 does not hold.
\*******************************************************************************

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

TypeInvParticipant  ==
  participant \in  [
    participants -> [
      vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in  [
    request   : [participants -> BOOLEAN],
    vote      : [participants -> {waiting, yes, no}],
    broadcast : [participants -> {commit, abort, notsent}],
    decision  : {commit, abort, undecided},
    alive     : BOOLEAN,
    faulty    : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* Initially:
\* All participants: no vote sent, undecided, alive, not faulty.
\* Coordinator: no request sent, waiting for votes, alive.
InitParticipant == participant \in [
  participants -> [
    vote     : {yes, no},
    alive    : {TRUE},
    decision : {undecided},
    faulty   : {FALSE},
    voteSent : {FALSE}
  ]
]

InitCoordinator == coordinator \in [
  request   : [participants -> {FALSE}],
  vote      : [participants -> {waiting}],
  broadcast : [participants -> {notsent}],
  decision  : {undecided},
  alive     : {TRUE},
  faulty    : {FALSE}
]

Init == InitParticipant /\ InitCoordinator

\* Coordinator: request a vote from a participant.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                                 [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED<<participant>>

\* Coordinator: record the vote that has arrived (a message it already has).
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote =
                                 [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED<<participant>>

\* Coordinator: time out on a dead participant and abort instead.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>

\* Coordinator: decide commit iff all votes are yes, else abort.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>

\* Coordinator: the simple broadcast; a series of messages, so not atomic.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

\* Participant: send its vote to the coordinator.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] =
                                    [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED<<coordinator>>

\* Participant: abort unilaterally on a no vote.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] =
                                       [@ EXCEPT !.decision = abort]]
                  /\ UNCHANGED<<coordinator>>

\* Participant: abort unilaterally on a coordinator that never asked.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] =
                                                [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED<<coordinator>>

\* Participant: adopt the broadcast decision.
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] =
                                  [@ EXCEPT !.decision = coordinator.broadcast[i]]]
             /\ UNCHANGED<<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] =
                                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED<<coordinator>>

\* Coordinators are treated as strongly fair; participants are only weakly fair.
coordProgB == makeDecision \/ \E i \in participants : request(i) \/ getVote(i)
                             \/ detectFault(i) \/ coordBroadcast(i)

coordProgN == coordDie \/ coordProgB

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY
\* All decisions agree, and commit only follows a unanimous yes.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

AC4 == [] (\A i \in participants : participant[i].decision = commit => [] participant[i].decision = commit)
          /\ (\A i \in participants : participant[i].decision = abort => [] participant[i].decision = abort)

\* LIVENESS
\* Decisions are always eventually reached or a failure is detected.
AC3_2 == <> (\A i \in participants : participant[i].decision \in {abort, commit})
               \/ (\E j \in participants : participant[j].faulty) \/ coordinator.faulty

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                    => (\A j \in participants : participant[j].vote = yes /\ coordinator.decision = commit)

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                      => \/ (\E j \in participants : participant[j].vote = no)
                         \/ (\E j \in participants : participant[j].faulty /\ coordinator.decision = abort)
                         \/ (coordinator.faulty /\ coordinator.decision = undecided)

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

====