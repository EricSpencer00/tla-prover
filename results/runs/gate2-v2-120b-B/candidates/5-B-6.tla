---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `Atomic Commitment Protocol' with Simple Broadcast primitive (ACP‑SB)
\* Adapted from Mullender & Toueg, Distributed Systems, Chapter 6.
\* This version uses a simple (asynchronous) broadcast and assumes
\* failures are detected magically.  Consequently the algorithm is
\* non‑terminating and the original termination property AC5 does not hold.

CONSTANTS
  participants,           \* set of participants
  yes, no,                \* possible votes
  undecided, commit, abort, \* decision values
  waiting,                \* coordinator’s vote‑state for a participant
  notsent                 \* broadcast state for a participant

VARIABLES
  participant,            \* map from each participant to its local state
  coordinator             \* coordinator’s state

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
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
\* ----------------------------------------------------------------------
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
\* ----------------------------------------------------------------------
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED << participant >>

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED << participant >>

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED << participant >>

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ (
        /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
     )
  /\ UNCHANGED << participant >>

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED << participant >>

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED << participant >>

\* ----------------------------------------------------------------------
\* Participant actions
\* ----------------------------------------------------------------------
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED << coordinator >>

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED << coordinator >>

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED << coordinator >>

decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED << coordinator >>

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED << coordinator >>

\* ----------------------------------------------------------------------
\* Composite actions for the model
\* ----------------------------------------------------------------------
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* ----------------------------------------------------------------------
\* Fairness (death transitions are left outside of fairness)
\* ----------------------------------------------------------------------
fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have voted YES
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes) )

\* If any participant decides abort, then at least one vote was NO, or a fault occurred
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty )

\* Each participant decides at most once
AC4 == [] ( /\ (\A i \in participants :
               participant[i].decision = commit => [] (participant[i].decision = commit))
           /\ (\A i \in participants :
               participant[i].decision = abort  => [] (participant[i].decision = abort)) )

\* ----------------------------------------------------------------------
\* Liveness (stronger version of AC3)
\* ----------------------------------------------------------------------
AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty )

\* ----------------------------------------------------------------------
\* Helper / intermediate properties (kept unchanged from the original spec)
\* ----------------------------------------------------------------------
FaultyStable ==
  /\ \A i \in participants : [](participant[i].faulty => []participant[i].faulty])
  /\ [](coordinator.faulty => []coordinator.faulty)

VoteStable ==
  \A i \in participants :
    \/ [](participant[i].vote = yes)
    \/ [](participant[i].vote = no)

StrongerAC2 ==
  [] ( (\E i \in participants : participant[i].decision = commit)
      => /\ (\A j \in participants : participant[j].vote = yes)
         /\ coordinator.decision = commit)

StrongerAC3_1 ==
  [] ( (\E i \in participants : participant[i].decision = abort)
      => \/ (\E j \in participants : participant[j].vote = no)
         \/ /\ \E j \in participants : participant[j].faulty
            /\ coordinator.decision = abort
         \/ /\ coordinator.faulty
            /\ coordinator.decision = undecided)

NoRecovery ==
  [] ( /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
       /\ coordinator.alive <=> ~coordinator.faulty)

\* ----------------------------------------------------------------------
\* Invalid / non‑terminating properties (kept for reference)
\* ----------------------------------------------------------------------
DecisionReachedNoFault ==
  (\A i \in participants : participant[i].alive) ~>
    (\A k \in participants : participant[k].decision # undecided)

AbortImpliesNoVote ==
  [] ( (\E i \in participants : participant[i].decision = abort)
        => (\E j \in participants : participant[j].vote = no) )

AC5 == <> \A i \in participants :
          \/ participant[i].decision \in {abort, commit}
          \/ participant[i].faulty

====