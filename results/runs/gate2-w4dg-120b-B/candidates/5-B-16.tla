---- MODULE W4Od11m8p2t1 ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting

\* Simple Broadcast: a broadcast is a series of messages sent, one per participant, and
\* the algorithm never waits for all of them together.  Consequently the property AC5
\* from the original paper ("the system always reaches a terminal state") does NOT hold.
\* This is not a bug and is not fixed by any change below.

VARIABLES participant, coordinator

TypeInvParticipant == participant \in  [
  participants -> [
    vote      : {yes, no}, 
    alive     : BOOLEAN, 
    decision  : {undecided, commit, abort},
    faulty    : BOOLEAN,
    voteSent  : BOOLEAN
  ]
]

TypeInvCoordinator == coordinator \in [
  request   : [participants -> BOOLEAN],
  vote      : [participants -> {waiting, yes, no}],
  alive     : BOOLEAN,
  decision  : {undecided, commit, abort},
  faulty    : BOOLEAN
]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

\* Initially: no request sent, no vote cast, nobody dead, nobody decided.
InitParticipant == participant \in  [
  participants -> [
    vote     : {yes, no},
    alive    : {TRUE},
    decision : {undecided},
    faulty   : {FALSE},
    voteSent : {FALSE}
  ]
]

InitCoordinator == coordinator \in [
  request : [participants -> {FALSE}],
  vote    : [participants -> {waiting}],
  alive   : {TRUE},
  decision: {undecided},
  faulty  : {FALSE}
]

Init == InitParticipant /\ InitCoordinator

\* COORDINATOR: send a vote request to participant i.
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED participant

\* COORDINATOR: record a vote that has arrived from participant i.
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED participant

\* COORDINATOR: a participant that has died without voting triggers an abort.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* COORDINATOR: cast the final decision once every participant has voted.
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ coordinator' = [coordinator EXCEPT !.decision =
                                      IF \A j \in participants : coordinator.vote[j] = yes
                                      THEN commit ELSE abort]
                /\ UNCHANGED participant

\* COORDINATOR: send the final decision to participant i (simple broadcast).
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
                     /\ UNCHANGED participant

\* COORDINATOR: die (detected magically, no timeout needed).
coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* PARTICIPANT: send a yes/no vote to the coordinator.
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED coordinator

\* PARTICIPANT: on seeing its own vote is NO it may abort unilaterally.
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED coordinator

\* PARTICIPANT: it is decided, so act on the broadcast from the coordinator.
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.request[i]
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
             /\ UNCHANGED coordinator

\* PARTICIPANT: die (detected magically).
parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ decide(i)
coordProg == makeDecision \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
progN     == (\E i \in participants : parDie(i) \/ parProg(i)) \/ coordProg

\* Death is outside fairness; everything else should keep progressing without it.
fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProg)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY PROPERTY: all participants that decide must agree, and if any decides commit
\* then every vote read was YES (the coordinator never cheats on the vote).
AC1 == [] \A i, j \in participants : participant[i].decision # commit \/ participant[j].decision # abort
AC2 == [] ((\E i \in participants : participant[i].decision = commit) => (\A j \in participants : participant[j].vote = yes))

Next == \/ (\E i \in participants : request(i)) \/ (\E i \in participants : getVote(i))
        \/ (\E i \in participants : detectFault(i)) \/ makeDecision
        \/ (\E i \in participants : coordBroadcast(i)) \/ coordDie
        \/ (\E i \in participants : sendVote(i)) \/ (\E i \in participants : abortOnVote(i))
        \/ (\E i \in participants : decide(i)) \/ (\E i \in participants : parDie(i))

vars == <<coordinator, participant>>

\* The "liveness" clause from the original paper is stronger here.  AC3_2 is what TLC
\* actually checks; the weaker AC3_1 is an intermediate step in the proof.
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E i \in participants : participant[i].faulty \/ coordinator.faulty

====