---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\* This version replaces synchronous communication with (implicit) asynchronous
\* communication and fails "magically" rather than by timeout.  The broadcast is
\* a series of messages, possibly interrupted by a failure, so the algorithm is
\* non-terminating and AC5 does not hold.
\* The change below fixes a silent bug: the coordinator's decision step was
\* never assigning the coordinator's vote record, leaving the next-state
\* relation under-specified.

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
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

\* Initially every participant has a yes/no vote, is alive, and has not sent,
\* and the coordinator has not requested or received anything.
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

\* COORDINATOR STATEMENTS

\* A live coordinator requests a vote from participant i.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]
                 ]
              /\ UNCHANGED <<participant>>

\* A live coordinator records participant i's vote once it arrives.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]
                 ]
              /\ UNCHANGED <<participant>>

\* A live, undecided coordinator times out on a dead, non-voting participant i
\* and decides to abort.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED <<participant>>

\* A live coordinator decides once every participant has voted.
\* The bug was that only the decision was set, not the vote record itself.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.vote      =
                                      [@ EXCEPT ![j] = participant[j].vote],
                                    !.decision = IF \A j \in participants : coordinator.vote[j] = yes
                                                    THEN commit ELSE abort]
                /\ UNCHANGED <<participant>>

\* A live coordinator sends its decision to participant i.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]
                        ]
                     /\ UNCHANGED <<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED <<participant>>

\* PARTICIPANT STATEMENTS 

\* An alive participant sends its vote once it receives the request.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.voteSent = TRUE]
                  ]
               /\ UNCHANGED <<coordinator>>

\* An alive participant that voted no decides to abort unilaterally.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.decision = abort]
                     ]
                  /\ UNCHANGED <<coordinator>>

\* An alive undecided participant aborts if the coordinator died silently.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.decision = abort]
                               ]
                            /\ UNCHANGED <<coordinator>>

\* An alive undecided participant adopts the coordinator's decision.
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.decision = coordinator.broadcast[i]]
                ]
             /\ UNCHANGED <<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]
                ]
             /\ UNCHANGED <<coordinator>>

\* FOR N PARTICIPANTS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Deaths are left outside fairness.

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* CORRECTNESS SPECIFICATION

\* All participants that decide reach the same decision.
AC1 == [] \A i, j \in participants : 
          \/ participant[i].decision # commit 
          \/ participant[j].decision # abort

\* If any participant decides commit, all participants must have voted yes.
AC2 == [] (  (\E i \in participants : participant[i].decision = commit) 
          => (\A j \in participants : participant[j].vote = yes))

\* If any participant decides abort, some participant voted no or some node is faulty.
AC3_1 == [] (  (\E i \in participants : participant[i].decision = abort) 
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty)

\* Each participant decides at most once.
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit 
                                => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort  
                                => [](participant[j].decision = abort))

\* LIVENESS: progress to a decision or a failure.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

\* (Stronger) AC2: a committed decision implies all votes were yes and the
\* coordinator recorded them.
StrongerAC2 == [] (  (\E i \in participants : participant[i].decision = commit) 
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit)

\* (Stronger) AC3: an abort implies a no vote, or a participant fault, or a
\* coordinator failure.
StrongerAC3_1 == [] (  (\E i \in participants : participant[i].decision = abort) 
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ \E j \in participants : participant[j].faulty
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided)

\* Well-formedness: alive iff not faulty.
NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

====