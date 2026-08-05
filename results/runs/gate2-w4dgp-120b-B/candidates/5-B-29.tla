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
\* This version of the protocol uses a "simple broadcast" where a broadcast is simply
\* a series of messages sent, possibly interrupted by a failure.  Consequently, this
\* algorithm is "non terminating" and property AC5 does not hold.
\*******************************************************************************

CONSTANTS
  participants,            \* set of participants
  yes, no,                 \* vote
  undecided, commit, abort, \* decision
  waiting,                 \* coordinator's vote-gathering stage wrt a participant
  notsent                  \* broadcast status wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

--------------------------------------------------------------------------------

TypeInvParticipant == participant \in [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
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

--------------------------------------------------------------------------------

\* Initially:
\* All participants have a vote, are alive and undecided, and have not sent anything.
\* The coordinator has requested nothing, is alive and undecided, and has broadcast nothing.

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

--------------------------------------------------------------------------------
\* Coordinator requests a vote from a participant.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED<<participant>>

\* Coordinator records a vote that has arrived.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                                 [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED<<participant>>

\* Coordinator times out on a participant that failed without voting.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>

\* Coordinator decides based on the votes it has.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>

\* Simple broadcast (a series of messages) of the decision.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

--------------------------------------------------------------------------------

\* A participant sends its vote.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = 
                                   [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED<<coordinator>>

\* A participant voting NO aborts immediately.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                                      [@ EXCEPT !.decision = abort]]
                  /\ UNCHANGED<<coordinator>>

\* A participant aborts if it timed out waiting for a request from a dead coordinator.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                                [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED<<coordinator>>

\* A participant follows the coordinator's broadcast.
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

--------------------------------------------------------------------------------

\* Synchronous participant steps (fairness applied to these only).
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

\* Synchronous coordinator steps (fairness applied to these only).
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

--------------------------------------------------------------------------------
\* SAFETY

\* All decided participants agree.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* Commit needs unanimous yes votes.
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* Abort needs a no vote or a failure.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* Decisions are made once.
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit
                        => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort
                        => [](participant[j].decision = abort))

--------------------------------------------------------------------------------
\* LIVENESS

\* At least one decision is reached, or someone is faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

--------------------------------------------------------------------------------
\* INTERMEDIATE PROPERTIES (used in proofs)

FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                /\ [](coordinator.faulty => [] coordinator.faulty)

VoteStable == \A i \in participants :
                \/ [](participant[i].vote = yes) \/ [](participant[i].vote = no)

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ \E j \in participants : participant[j].faulty
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided)

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

================================================================================