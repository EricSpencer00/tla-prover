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
  participants,                 \* set of participants
  yes, no,                      \* vote values
  undecided, commit, abort,     \* decision values
  waiting,                      \* coordinator state wrt a participant
  notsent                       \* broadcast state wrt a participant

VARIABLES
  participant,                 \* map from participants to their local state
  coordinator                  \* coordinator state

\* ---------------------------------------------------------------------------

\* Types (useful for debugging, not part of the spec's behavior)
TypeInvParticipant ==
  participant \in [participants -> [
    vote      : {yes, no},
    alive     : BOOLEAN,
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    voteSent  : BOOLEAN
  ]]

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

\* ---------------------------------------------------------------------------

\* Initial state
InitParticipant ==
  participant = [i \in participants |-> [
    vote     |-> IF i = "p1" THEN yes ELSE IF i = "p2" THEN yes ELSE yes, \* concrete votes are chosen by the cfg
    alive    |-> TRUE,
    decision |-> undecided,
    faulty   |-> FALSE,
    voteSent |-> FALSE
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

Init == InitParticipant /\ InitCoordinator

\* ---------------------------------------------------------------------------
\* COORDINATOR ACTIONS

\* Send vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Record vote from participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Detect fault of participant i and abort
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Decide commit or abort based on collected votes
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ IF \A j \in participants : coordinator.vote[j] = yes
        THEN coordinator' = [coordinator EXCEPT !.decision = commit]
        ELSE coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Broadcast the decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* Coordinator dies
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

\* ---------------------------------------------------------------------------
\* PARTICIPANT ACTIONS

\* Participant i sends its vote
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* Participant i aborts because its vote is no
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i aborts because request never arrived (coordinator dead)
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i decides according to coordinator's broadcast
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Participant i dies
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

\* ---------------------------------------------------------------------------
\* COMPOSITE ACTIONS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == (\E i \in participants : parDie(i)) \/ (\E i \in participants : parProg(i))

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ (\E i \in participants : coordProgA(i))

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Fairness assumptions (left unchanged)
fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

\* ---------------------------------------------------------------------------
\* SPECIFICATION

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* ---------------------------------------------------------------------------
\* SAFETY INVARIANTS

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have voted YES
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes) )

\* If any participant decides abort, then at least one voted NO or someone is faulty
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
              => \/ (\E j \in participants : participant[j].vote = no)
                 \/ (\E j \in participants : participant[j].faulty)
                 \/ coordinator.faulty )

\* Each participant decides at most once
AC4 == [] ( \A i \in participants :
            (participant[i].decision = commit => [] (participant[i].decision = commit))
            /\ (participant[i].decision = abort  => [] (participant[i].decision = abort)) )

=============================================================================