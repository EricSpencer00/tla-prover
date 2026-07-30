---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor. Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by
\* `^\"O. Babao\u{g}lu and S. Toueg.^' 1993.
\*
\* This version replaces synchronous communication with an implicit
\* asynchronous "simple broadcast": a broadcast is a series of messages
\* that may be interrupted by a failure, so the algorithm is
\* non-terminating (AC5 does not hold).  Failures are detected "magically"
\* rather than via timeouts.
\*

CONSTANTS
  participants,   \* set of participants
  yes, no,         \* vote
  undecided, commit, abort, \* decision
  waiting,        \* coordinator state wrt a participant
  notsent         \* broadcast state wrt a participant

VARIABLES
  participant, \* [participants -> [vote: {yes,no}, alive: BOOLEAN,
  \*                decision: {undecided,commit,abort}, faulty: BOOLEAN,
  \*                voteSent: BOOLEAN]]
  coordinator  \* [request: [participants -> BOOLEAN], vote:
  \*                [participants -> {waiting, yes, no}], broadcast:
  \*                [participants -> {commit, abort, notsent}], decision:
  \*                {commit, abort, undecided}, alive: BOOLEAN,
  \*                faulty: BOOLEAN]

TypeInvParticipant == participant \in [
  participants -> [vote: {yes, no}, alive: BOOLEAN,
    decision: {undecided, commit, abort}, faulty: BOOLEAN,
    voteSent: BOOLEAN]]

TypeInvCoordinator == coordinator \in [
  request: [participants -> BOOLEAN],
  vote: [participants -> {waiting, yes, no}],
  broadcast: [participants -> {commit, abort, notsent}],
  decision: {commit, abort, undecided},
  alive: BOOLEAN,
  faulty: BOOLEAN]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant == participant \in [
  participants -> [vote |-> yes, alive |-> TRUE,
    decision |-> undecided, faulty |-> FALSE, voteSent |-> FALSE]]

InitCoordinator == coordinator \in [
  request |-> [p \in participants |-> FALSE],
  vote |-> [p \in participants |-> waiting],
  broadcast |-> [p \in participants |-> notsent],
  decision |-> undecided, alive |-> TRUE, faulty |-> FALSE]

Init == InitParticipant /\ InitCoordinator

\* Coordinator requests a vote from participant i.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
              /\ UNCHANGED participant

\* Coordinator records i's vote once the vote message has arrived.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
              /\ UNCHANGED participant

\* Coordinator detects that a participant died without voting, times out,
\* and decides to abort.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* Coordinator decides commit only if all votes are yes; otherwise abort.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                     IF \A j \in participants : coordinator.vote[j] = yes
                     THEN commit ELSE abort]
                /\ UNCHANGED participant

\* Simple broadcast: the coordinator sends its decision to participant i.
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT
                          !.broadcast[i] = coordinator.decision]
                     /\ UNCHANGED participant

\* Coordinator crashes (becomes faulty).
coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* Participant i sends its vote to the coordinator.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

\* A participant that has voted no unilaterally aborts.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

\* A participant aborts when its coordinator has died before requesting.
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED coordinator

\* A participant decides on the coordinator's broadcast.
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT
                  ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED coordinator

\* A participant crashes (becomes faulty).
parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
             /\ UNCHANGED coordinator

\* Participant-level actions (parameterized by i).
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Death actions are left outside fairness: a participant or coordinator may
\* crash silently and permanently.
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY

\* All participants that decide reach the same decision.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* Commit only when every participant's vote was yes.
AC2 == [] (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* Abort only if some participant voted no, some participant is faulty, or
\* the coordinator is faulty.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* Each participant decides at most once (a standard trick).
AC4 == [] /\ (\A i \in participants :
                participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants :
                participant[i].decision = abort => [](participant[i].decision = abort))

\* LIVENESS

\* A decision is eventually reached by somebody, or some participant or the
\* coordinator is found to be faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty \/ coordinator.faulty

\* Intermediate properties used in proofs (not checked directly).
FaultyStable == /\ (\A i \in participants : participant[i].faulty => [] participant[i].faulty)
                /\ coordinator.faulty => [] coordinator.faulty

VoteStable == \A i \in participants : [] (participant[i].vote = yes \/ participant[i].vote = no)

StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit)
                  => /\ (\A j \in participants : participant[j].vote = yes)
                     /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort)
                    => \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ (\E j \in participants : participant[j].faulty)
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided

NoRecovery == [] /\ (\A i \in participants : participant[i].alive <=> ~participant[i].faulty)
                 /\ coordinator.alive <=> ~coordinator.faulty

\* INVALID (failing) properties retained for discrimination only:
DecisionReachedNoFault == (\A i \in participants : participant[i].alive) ~> (\A k \in participants : participant[k].decision # undecided)
AbortImpliesNoVote == [] (\E i \in participants : participant[i].decision = abort) => (\E j \in participants : participant[j].vote = no)
AC5 == <> \A i \in participants :
           \/ participant[i].decision \in {abort, commit} \/ participant[i].faulty

====