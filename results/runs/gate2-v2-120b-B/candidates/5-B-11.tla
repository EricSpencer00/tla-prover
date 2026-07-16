---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>

\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB)
\* From:
\* `^Sape Mullender^', editor.  Distributed Systems.
\* Chapter 6: Non-Blocking Atomic Commitment, by `^"O. Babao\u{g}lu and S. Toueg.^'
\* 1993.

\*******************************************************************************
\* Synchronous communication has been replaced with (implicit) asynchronous communication.
\* Failures are detected "magically" instead of relying on timeouts.
\*
\* This version of the protocol uses a "simple broadcast" where a broadcast is simply a 
\* series of messages sent, possibly interrupted by a failure. Consequently, this algorithm
\* is "non terminating" and property AC5 does not hold.
\*******************************************************************************

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

--------------------------------------------------------------------------------

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
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {commit, abort, undecided},
  alive     : BOOLEAN,
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

--------------------------------------------------------------------------------

\* Initially:
\* All participants have a yes/no vote, are alive and not faulty,
\* have not sent their votes yet, and are undecided.
\* The coordinator has not sent any requests, has not received votes,
\* is alive and not faulty, has not broadcast any decision, and is undecided.

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
  broadcast : [participants -> {notsent}],
  decision  : {undecided},
  alive     : {TRUE},
  faulty    : {FALSE}
]

Init == InitParticipant /\ InitCoordinator

--------------------------------------------------------------------------------
\* COORDINATOR ACTIONS

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                                 [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED << participant >>

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote =
                                 [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED << participant >>

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED << participant >>

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED << participant >>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                                        [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED << participant >>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE,
                                            !.faulty = TRUE]
            /\ UNCHANGED << participant >>

--------------------------------------------------------------------------------
\* PARTICIPANT ACTIONS

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] =
                                   [@ EXCEPT !.voteSent = TRUE]]
               /\ UNCHANGED << coordinator >>

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] =
                                      [@ EXCEPT !.decision = abort]]
                  /\ UNCHANGED << coordinator >>

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] =
                                                [@ EXCEPT !.decision = abort]]
                            /\ UNCHANGED << coordinator >>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] =
                                 [@ EXCEPT !.decision = coordinator.broadcast[i]]]
             /\ UNCHANGED << coordinator >>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] =
                                 [@ EXCEPT !.alive = FALSE,
                                         !.faulty = TRUE]]
             /\ UNCHANGED << coordinator >>

--------------------------------------------------------------------------------
\* COMBINED ACTIONS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \/ \E i \in participants : parDie(i)
            \/ \E i \in participants : parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

--------------------------------------------------------------------------------
\* FAIRNESS (outside of safety)

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

--------------------------------------------------------------------------------
\* SAFETY INVARIANTS

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants must have voted YES
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes) )

\* If any participant decides abort, then at least one vote was NO, or a participant is
\* faulty, or the coordinator is faulty
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
              => \/ (\E j \in participants : participant[j].vote = no)
                 \/ (\E j \in participants : participant[j].faulty)
                 \/ coordinator.faulty )

\* Each participant decides at most once
AC4 == [] ( /\ (\A i \in participants :
               participant[i].decision = commit => [] (participant[i].decision = commit))
           /\ (\A i \in participants :
               participant[i].decision = abort => [] (participant[i].decision = abort)) )

--------------------------------------------------------------------------------
\* LIVENESS

AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
              \/ \E i \in participants : participant[i].faulty
              \/ coordinator.faulty )

================================================================================