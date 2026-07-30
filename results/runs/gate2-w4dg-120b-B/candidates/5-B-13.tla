---- MODULE ACP_SB ----
\* Time-stamp: <10 Jun 2002 at 12:39:50 by charpov on berlioz.cs.unh.edu>
\* `^Atomic Committment Protocol^' with Simple Broadcast primitive (ACP-SB).
\* This version corrects an incompletely specified action (makeDecision) so
\* TLC can generate successor states; all other semantics are unchanged.
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting,
          notsent

VARIABLES participant, coordinator

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
    alive     : {TRUE},
    broadcast : [participants -> {notsent}],
    decision  : {undecided},
    faulty    : {FALSE}
  ]

Init == InitParticipant /\ InitCoordinator

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request =
                     [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED <<participant>>

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED <<participant>>

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant>>

\* The decision is a genuine outcome (commit only on unanimity), so it
\* must always be copied into the coordinator's broadcast map before the
\* coordinator itself can clear its decision field.
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT
        !.decision = IF \A j \in participants : coordinator.vote[j] = yes THEN commit ELSE abort,
        !.broadcast = [participants -> coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED <<participant>>

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED <<participant>>

sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED <<coordinator>>

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED <<coordinator>>

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED <<coordinator>>

decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED <<coordinator>>

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)
coordProgN == coordDie \/ coordProgB
progN == parProgN \/ coordProgN

ProgFairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ ProgFairness

\* SAFETY: all participants that decide agree, and a commit decision
\* is unanimous.  A decision to abort is explained by a NO vote or a
\* failure.  Each participant decides at most once.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] (\E i \in participants : participant[i].decision = commit)
         => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
           => ( \/ \E j \in participants : participant[j].vote = no
               \/ \E j \in participants : participant[j].faulty
               \/ coordinator.faulty)

AC4 == [] /\ (\A i \in participants : participant[i].decision = commit
                => [] participant[i].decision = commit)
          /\ (\A j \in participants : participant[j].decision = abort
                => [] participant[j].decision = abort)

\* LIVENESS: some participant eventually decides, and the coordinator
\* recovers from being marked faulty back to alive.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

Repairable == <> /\ coordinator.alive

====