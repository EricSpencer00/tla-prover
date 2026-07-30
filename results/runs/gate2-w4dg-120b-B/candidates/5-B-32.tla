---- MODULE ACP_SB_f2m3p1t1 ----
EXTENDS Integers, FiniteSets

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

\* The action makeDecision fails to assign coordinator.decision, so the whole state
\* lands in an absurd null value.  The fix is an ordinary assignment, not a
\* semantic weakening.
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
  broadcast : [participants -> {commit, abort, notsent}],
  decision  : {commit, abort, undecided},
  alive     : BOOLEAN,
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
  broadcast |-> [p \in participants |-> notsent],
  decision  |-> undecided,
  alive     |-> TRUE,
  faulty    |-> FALSE
]

Init == InitParticipant /\ InitCoordinator

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED <<participant>>

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED <<participant>>

detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED <<participant>>

\* The missing assignment: coordinator.decision is set where it is decided.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                      IF \A j \in participants : coordinator.vote[j] = yes
                      THEN commit ELSE abort]
                /\ UNCHANGED <<participant>>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast =
                          [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED <<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED <<participant>>

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED <<coordinator>>

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED <<coordinator>>

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED <<coordinator>>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED <<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED <<coordinator>>

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)
coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)
coordProgN == coordDie \/ coordProgB
progN == parProgN \/ coordProgN

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY

\* All participants that decide reach the same decision.
AC1 == [] \A i, j \in participants :
          \/ participant[i].decision # commit
          \/ participant[j].decision # abort

\* A commit decision at least one participant voted yes.
AC2 == [] (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes)

\* An abort decision has a no vote, a faulty participant, or a faulty coordinator.
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => \/ (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty

\* Each participant decides at most once.
AC4 == [] (\A i \in participants : participant[i].decision = commit => [] (participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort => [] (participant[i].decision = abort))

\* LIVENESS

\* Every participant eventually decides or is faulty.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

====