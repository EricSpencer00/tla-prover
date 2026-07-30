---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^\"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\* Synchronous communication has been replaced with (implicit) asynchronous
\* communication, and failures are detected "magically".  This version of the
\* protocol uses a "simple broadcast": a broadcast is a series of messages sent,
\* possibly interrupted by a failure, so the algorithm is non-terminating and
\* AC5 does not hold.

CONSTANTS
  participants, yes, no, undecided, commit, abort, waiting, notsent

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
  alive     : BOOLEAN,
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {undecided, commit, abort},
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
  alive     |-> TRUE,
  broadcast |-> [p \in participants |-> notsent],
  decision  |-> undecided,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

\* Coordinator sends a vote request to participant i
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

\* Coordinator records the vote of participant i whose vote message arrived
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote =
                   [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

\* Coordinator times out on a participant i that died silently and decides abort
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* Coordinator decides once it has all votes
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                     IF \A j \in participants : coordinator.vote[j] = yes
                     THEN commit ELSE abort]
                /\ UNCHANGED participant

\* Simple broadcast: coordinator sends its decision to participant i
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* Participant sends its vote
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

\* Participant aborts on its own no vote
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

\* Participant aborts when the coordinator dies silently
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

\* Participant adopts the coordinator's broadcast decision
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* Any commit decision is backed by all voters saying yes
AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => \A j \in participants : participant[j].vote = yes

\* An abort decision occurs only if some participant voted no or some node died
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
           => \/ (\E j \in participants : participant[j].vote = no)
              \/ (\E j \in participants : participant[j].faulty)
              \/ coordinator.faulty

\* Each participant decides at most once
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit
                               => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort
                               => [](participant[j].decision = abort))

\* LIVENESS (stronger for AC3 than the original paper)
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

\* (SOME) INTERMEDIATE PROPERTIES

FaultyStable == /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty)
                /\ [](coordinator.faulty => []coordinator.faulty)

VoteStable == \A i \in participants :
                \/ [] (participant[i].vote = yes)
                \/ [] (participant[i].vote = no)

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                 => /\ \A j \in participants : participant[j].vote = yes
                    /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                   => \/ (\E j \in participants : participant[j].vote = no)
                      \/ /\ \E j \in participants : participant[j].faulty
                         /\ coordinator.decision = abort
                      \/ /\ coordinator.faulty
                         /\ coordinator.decision = undecided

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

\* (SOME) INVALID PROPERTIES

DecisionReachedNoFault == (\A i \in participants : participant[i].alive)
                          ~> (\A k \in participants : participant[k].decision # undecided)
AbortImpliesNoVote == [] (\E i \in participants : participant[i].decision = abort)
                        => (\E j \in participants : participant[j].vote = no)
\* Broadcast termination does not hold here; this algorithm may never finish
\* broadcasting to every participant, so AC5 is not a property.
====