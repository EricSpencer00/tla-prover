---- MODULE ACP_SB ----
EXTENDS Integers

\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\* Synchronous communication has been replaced with (implicit) asynchronous communication.
\* Failures are detected "magically" instead or relying on timeouts.
\*
\* This version of the protocol uses a "simple broadcast" where a broadcast is simply a 
\* series of messages sent, possibly interrupted by a failure.  Consequently, this algorithm
\* is "non terminating" and property AC5 does not hold.

CONSTANTS
  participants,
  yes, no,
  undecided, commit, abort,
  waiting,
  notsent

VARIABLES
  participant,   \* participants
  coordinator    \* coordinator

TypeInvParticipant == participant \in  [
  participants -> [
    vote     : {yes, no},
    alive    : BOOLEAN,
    decision : {undecided, commit, abort},
    faulty   : BOOLEAN,
    voteSent : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in  [
  request   : [participants -> BOOLEAN],
  vote      : [participants -> {waiting, yes, no}],
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {commit, abort, undecided},
  alive     : BOOLEAN,
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* Initially all participants are alive, undecided, and have not sent a vote yet.
\* The coordinator is alive, undecided, and has not sent requests or messages.
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
  alive     : {TRUE},
  broadcast : [participants -> {notsent}],
  decision  : {undecided},
  faulty    : {FALSE}
]

Init == InitParticipant /\ InitCoordinator

\* Coordinator asks for votes.  Each ask is a separate request.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED<<participant>>

\* Coordinator records a vote once it has been sent.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED<<participant>>

\* A dead participant that has not sent a vote is timed out and leads to abort.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>

\* The coordinator decides when all votes are in.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes,no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>

\* Simple broadcast: the coordinator sends its decision to each participant.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

\* Participants send their votes once they have received a request.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED<<coordinator>>

\* A participant may abort on its own if its vote is no.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                  /\ UNCHANGED<<coordinator>>

\* A participant times out waiting for the dead coordinator's request and aborts.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED<<coordinator>>

\* A participant adopts the coordinator's decision once it is received.
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
             /\ UNCHANGED<<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED<<coordinator>>

\* One participant dies.
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == (\E i \in participants : parDie(i) \/ parProg(i)) \/ coordProgN

\* Deaths are left out of fairness so that a live-only run is still fair.
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: all participants that decide, decide the same; commit needs all yes votes.

AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* Abort needs a no vote, a faulty participant, or a dead coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* At most one final decision per participant.
AC4 == [] (\A i \in participants :
              \/ (participant[i].decision = commit => [](participant[i].decision = commit))
              \/ (participant[i].decision = abort =>  [] (participant[i].decision = abort)))

\* LIVENESS: with no failures, some participant eventually decides.
AC3_2 == <> (\A i \in participants : participant[i].decision \in {abort, commit}
                           \/ \E j \in participants : participant[j].faulty
                           \/ coordinator.faulty)

StrongAC2 == [] (\E i \in participants : participant[i].decision = commit)
                   => /\ (\A j \in participants : participant[j].vote = yes)
                      /\ coordinator.decision = commit

StrongAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                     => \/ (\E j \in participants : participant[j].vote = no)
                        \/ (/\ \E j \in participants : participant[j].faulty
                             /\ coordinator.decision = abort)
                        \/ (/\ coordinator.faulty /\ coordinator.decision = undecided)

NoRecovery == [] (\A i \in participants : participant[i].alive <=> ~participant[i].faulty)
                    /\ (coordinator.alive <=> ~coordinator.faulty)

====