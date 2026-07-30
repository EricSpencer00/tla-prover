---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From `^Distributed Systems^', 1993, Chapter 6, by `^\"O. Babao\u{g}lu and S. Toueg.^'

\* Synchronous communication has been replaced by an (implicit) asynchronous
\* "simple broadcast": a broadcast is a series of messages sent, possibly
\* interrupted by a failure.  This algorithm is non terminating, so AC5 does
\* not hold.

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant == participant \in [
  participants -> [
    vote     : {yes, no}, alive    : BOOLEAN, decision : {undecided, commit, abort},
    faulty   : BOOLEAN, voteSent : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in [
  request   : [participants -> BOOLEAN], vote      : [participants -> {waiting, yes, no}],
  broadcast : [participants -> {commit, abort, notsent}], decision  : {commit, abort, undecided},
  alive     : BOOLEAN, faulty   : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [
  participants -> [
    vote     |-> yes, alive    |-> TRUE, decision |-> undecided,
    faulty   |-> FALSE, voteSent |-> FALSE
  ]
]

InitCoordinator == coordinator \in [
  request   |-> [participants |-> FALSE], vote      |-> [participants |-> waiting],
  broadcast |-> [participants |-> notsent], decision  |-> undecided,
  alive     |-> TRUE, faulty   |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

getVote(i) == /\ coordinator.alive /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

detectFault(i) == /\ coordinator.alive /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting /\ ~participant[i].alive /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

makeDecision == /\ coordinator.alive /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED participant

coordBroadcast(i) == /\ coordinator.alive /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED participant

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

sendVote(i) == /\ participant[i].alive /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

abortOnVote(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                  /\ participant[i].voteSent /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) == /\ participant[i].alive /\ participant[i].decision = undecided
                            /\ ~coordinator.alive /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

decide(i) == /\ participant[i].alive /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, !.faulty = TRUE]
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

\* SAFETY: all participants that decide reach the same decision, and commit
\* only follows a unanimous yes vote.  The abort clause is stronger than in
\* the original paper: aborting needs a no vote or a faulty participant.

AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
           => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
           => \/ (\E j \in participants : participant[j].vote = no)
              \/ (\E j \in participants : participant[j].faulty)
              \/ coordinator.faulty

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort  => [](participant[i].decision = abort))

\* LIVENESS: a decision (or a failure) is always eventually reached.

AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

\* INTERMEDIATE HELPERS

FaultyStable == /\ \A i \in participants : (participant[i].faulty => [] participant[i].faulty)
                /\ (coordinator.faulty => [] coordinator.faulty)

VoteStable == \A i \in participants : [] (participant[i].vote = yes) \/ [] (participant[i].vote = no)

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ \E j \in participants : participant[j].faulty
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                 /\ coordinator.alive <=> ~coordinator.faulty

\* INVALID: the following does not hold, so it is not a spec but a counterexample
\* of the original algorithm's termination claim.

AC5 == <> \A i \in participants : \/ participant[i].decision \in {abort, commit}
                                  \/ participant[i].faulty

====