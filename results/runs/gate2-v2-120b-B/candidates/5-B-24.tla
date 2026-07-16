---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `Atomic Commitment Protocol' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `Distributed Systems' edited by Sape Mullender.
\* Chapter 6: Non-Blocking Atomic Commitment, by O. Babaoğlu and S. Toueg, 1993.

\*---------------------------------------------------------------------------
\* This version replaces synchronous communication with (implicit) asynchronous
\* communication. Failures are detected "magically" instead of relying on
\* timeouts. The algorithm uses a "simple broadcast": a broadcast is a series
\* of messages sent, possibly interrupted by a failure. Consequently the
\* algorithm is non‑terminating and property AC5 does not hold.
\*---------------------------------------------------------------------------
              
CONSTANTS
  participants,                 \* set of participants
  yes, no,                      \* possible votes
  undecided, commit, abort,    \* possible decisions
  waiting,                      \* coordinator's per‑participant vote state
  notsent                       \* per‑participant broadcast state

VARIABLES
  participant,                  \* map from participants to their state
  coordinator,                  \* coordinator's state
  participantsSet               \* auxiliary variable to hold the constant set

\*---------------------------------------------------------------------------
\* Types
\*---------------------------------------------------------------------------
TypeInvParticipant ==
  participant \in [
    participants -> [
      vote      : {yes, no},
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      faulty    : BOOLEAN,
      voteSent  : BOOLEAN
    ]
  ]

TypeInvCoordinator ==
  coordinator \in [
    request    : [participants -> BOOLEAN],
    vote       : [participants -> {waiting, yes, no}],
    broadcast  : [participants -> {commit, abort, notsent}],
    decision   : {undecided, commit, abort},
    alive      : BOOLEAN,
    faulty     : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\*---------------------------------------------------------------------------
\* Initial state
\*---------------------------------------------------------------------------
InitParticipant ==
  participant = [i \in participants |-> [
    vote      |-> IF i = "p1" THEN yes ELSE yes,   \* all yes for simplicity
    alive     |-> TRUE,
    decision  |-> undecided,
    faulty    |-> FALSE,
    voteSent  |-> FALSE
  ]]

InitCoordinator ==
  coordinator = [
    request   |-> [i \in participants |-> FALSE],
    vote      |-> [i \in participants |-> waiting],
    broadcast |-> [i \in participants |-> notsent],
    decision  |-> undecided,
    alive     |-> TRUE,
    faulty    |-> FALSE
  ]

Init == /\ participantsSet = participants
        /\ InitParticipant
        /\ InitCoordinator
        /\ TypeInv

\*---------------------------------------------------------------------------
\* Actions
\*---------------------------------------------------------------------------
\* 1. Coordinator sends a request for a vote to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* 2. Coordinator records a vote received from participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* 3. Coordinator detects a fault (participant i died without voting) and aborts
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* 4. Coordinator makes a final decision once all votes are known
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ IF \A j \in participants : coordinator.vote[j] = yes
        THEN coordinator' = [coordinator EXCEPT !.decision = commit]
        ELSE coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* 5. Coordinator broadcasts its decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* 6. Coordinator dies
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

\* 7. Participant sends its vote to the coordinator
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* 8. Participant aborts on its own vote being NO
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* 9. Participant aborts because coordinator died before sending request
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* 10. Participant decides according to the coordinator's broadcast
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* 11. Participant dies
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

\*---------------------------------------------------------------------------
\* Combined actions
\*---------------------------------------------------------------------------
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i) \/ parDie(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == \E i \in participants : parProg(i) \/ coordProgN

\*---------------------------------------------------------------------------
\* Fairness assumptions (unchanged)
\*---------------------------------------------------------------------------
fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

\*---------------------------------------------------------------------------
\* Specification
\*---------------------------------------------------------------------------
Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\*---------------------------------------------------------------------------
\* Safety properties
\*---------------------------------------------------------------------------
\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have voted YES
AC2 == [] (  (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes))

\* If any participant decides abort, then at least one voted NO, or some
\* participant or the coordinator is faulty
AC3_1 == [] (  (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty)

\* Each participant decides at most once
AC4 == [] /\ (\A i \in participants :
                (participant[i].decision = commit) => [] (participant[i].decision = commit))
          /\ (\A i \in participants :
                (participant[i].decision = abort)  => [] (participant[i].decision = abort))

\*---------------------------------------------------------------------------
\* Liveness (unchanged)
\*---------------------------------------------------------------------------
AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty)

=============================================================================