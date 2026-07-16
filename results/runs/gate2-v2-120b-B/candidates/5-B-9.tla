---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets, TLC

\*  Original constants (kept unchanged)
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

\*  Types (unchanged)
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
    decision  : {commit, abort, undecided},
    alive     : BOOLEAN,
    faulty    : BOOLEAN
  ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\*  Initial state (unchanged)
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

\*-------------------------------------------------
\*  Actions (only the one that caused the error is
\*  modified; all others are unchanged)
\*-------------------------------------------------

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
  /\ UNCHANGED participant

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\*  The original makeDecision action did not assign the
\*  entire coordinator record, leaving the variable
\*  partially unspecified.  The corrected version updates
\*  the whole record, preserving the values of fields that
\*  are not changed.
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ (
        /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [
            request   |-> coordinator.request,
            vote      |-> coordinator.vote,
            broadcast |-> coordinator.broadcast,
            decision  |-> commit,
            alive     |-> coordinator.alive,
            faulty    |-> coordinator.faulty
          ]
     \/ 
        /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [
            request   |-> coordinator.request,
            vote      |-> coordinator.vote,
            broadcast |-> coordinator.broadcast,
            decision  |-> abort,
            alive     |-> coordinator.alive,
            faulty    |-> coordinator.faulty
          ]
     )
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

\* Participant actions (unchanged)
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.voteSent = TRUE]]
  /\ UNCHANGED coordinator

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
  /\ UNCHANGED coordinator

decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = coordinator.broadcast[i]]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
  /\ UNCHANGED coordinator

\* Composite actions
parProg(i) == \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
parProgN   == (\/ \E i \in participants : parDie(i)) \/ (\/ \E i \in participants : parProg(i))

coordProgA(i) == \/ request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB    == \/ makeDecision \/ (\/ \E i \in participants : coordProgA(i))
coordProgN    == \/ coordDie \/ coordProgB

progN == \/ parProgN \/ coordProgN

\* Fairness (unchanged)
fairness ==
  /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
  /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\*-------------------------------------------------
\*  Safety properties (unchanged)
\*-------------------------------------------------
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes))

AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
              => \/ (\E j \in participants : participant[j].vote = no)
                 \/ (\E j \in participants : participant[j].faulty)
                 \/ coordinator.faulty)

AC4 == [] ( /\ (\A i \in participants : participant[i].decision = commit => [] (participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort => [] (participant[j].decision = abort)) )

\*-------------------------------------------------
\*  Liveness (unchanged)
\*-------------------------------------------------
AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {abort, commit}
               \/ \E j \in participants : participant[j].faulty
               \/ coordinator.faulty )

====