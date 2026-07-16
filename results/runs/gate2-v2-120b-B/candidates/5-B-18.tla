---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `Atomic Commitment Protocol' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `Distributed Systems' edited by Sape Mullender.
\* Chapter 6: Non-Blocking Atomic Commitment, by O. Babaoğlu and S. Toueg, 1993.

\* This version replaces synchronous communication with (implicit) asynchronous
\* communication and assumes failures are detected magically.  The algorithm
\* therefore does not guarantee termination; property AC5 does not hold.

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* possible votes
  undecided, commit, abort, \* possible decisions
  waiting,                  \* coordinator's per‑participant vote state
  notsent                   \* per‑participant broadcast state

VARIABLES
  participant, \* participants (indexed map)
  coordinator  \* coordinator (record)

\* ----------------------------------------------------------------------
\* Types

TypeInvParticipant ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN
    ]
  ]

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

\* ----------------------------------------------------------------------
\* Initialization

InitParticipant ==
  participant \in [
    participants -> [
      vote     : {yes, no},
      alive    : {TRUE},
      decision : {undecided},
      faulty   : {FALSE},
      voteSent : {FALSE}
    ]
  ]

InitCoordinator ==
  coordinator \in [
    request   : [participants -> {FALSE}],
    vote      : [participants -> {waiting}],
    broadcast : [participants -> {notsent}],
    decision  : {undecided},
    alive     : {TRUE},
    faulty    : {FALSE}
  ]

Init == InitParticipant /\ InitCoordinator

\* ----------------------------------------------------------------------
\* Coordinator actions

\* Send a request for a vote to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED participant

\* Record the vote received from participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED participant

\* Detect a fault (participant i dead before voting) and abort
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Decide commit or abort after all votes are in
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
          /\ coordinator' = [coordinator EXCEPT !.decision = commit]
       \/ /\ \E j \in participants : coordinator.vote[j] = no
          /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Simple broadcast of the final decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED participant

\* Coordinator crashes
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

\* ----------------------------------------------------------------------
\* Participant actions

\* Send vote to coordinator (once)
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED coordinator

\* Unilaterally abort after sending a NO vote
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* Abort if coordinator never requested a vote (because it died)
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

\* Adopt the coordinator's broadcast decision
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED coordinator

\* Participant crashes
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED coordinator

\* ----------------------------------------------------------------------
\* Composite actions (for brevity)

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN ==
  \/ \E i \in participants : parDie(i)
  \/ \E i \in participants : parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Fairness (outside of liveness properties)
fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* ----------------------------------------------------------------------
\* Safety properties

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants voted YES
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes) )

\* If any participant decides abort, then at least one participant voted NO
\* or at least one participant is faulty, or the coordinator is faulty
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty )

\* Each participant decides at most once (once decided, stays that way)
AC4 == [] /\ (\A i \in participants :
                participant[i].decision = commit
                => [](participant[i].decision = commit))
          /\ (\A i \in participants :
                participant[i].decision = abort
                => [](participant[i].decision = abort))

\* ----------------------------------------------------------------------
\* Liveness property (optional, not used for safety)

AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
               \/ \E i \in participants : participant[i].faulty
               \/ coordinator.faulty )

=============================================================================