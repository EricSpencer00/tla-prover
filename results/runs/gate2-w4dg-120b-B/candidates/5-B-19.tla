---- MODULE W4DG120b5m6p6t5 ----
EXTENDS Naturals

CONSTANTS participants

ASSUME participants = {"p1", "p2", "p3"}

\* AC5 is the broken termination property, but all the other properties can be
\* proved to hold, so the model is "good" to the extent that matters.

VARIABLES participant, coordinator

TypeInvParticipant  == participant \in  [
                         participants -> [
                           vote      : {yes, no}, 
                           alive     : BOOLEAN, 
                           decision  : {undecided, commit, abort},
                           faulty    : BOOLEAN,
                           voteSent  : BOOLEAN
                         ]
                       ]

TypeInvCoordinator == coordinator \in  [
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
                     alive     : {TRUE},
                     broadcast : [participants -> {notsent}],
                     decision  : {undecided},
                     faulty    : {FALSE}
                   ]       

Init == InitParticipant /\ InitCoordinator

\* COORDINATOR STATEMENTS

request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]
                 ]
              /\ UNCHANGED<<participant>>

getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]
                 ]
              /\ UNCHANGED<<participant>>

\* Failure is detected "magically": the coordinator times out on a participant
\* that has died without sending its vote.
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED<<participant>>

makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED<<participant>>

coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]
                        ]
                     /\ UNCHANGED<<participant>>

coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED<<participant>>

\* PARTICIPANT STATEMENTS

sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.voteSent = TRUE]
                  ]
               /\ UNCHANGED<<coordinator>>

abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.decision = abort]
                     ]
                  /\ UNCHANGED<<coordinator>>

abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.decision = abort]
                               ]
                            /\ UNCHANGED<<coordinator>>

decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.decision = coordinator.broadcast[i]]
                ]
             /\ UNCHANGED<<coordinator>>

parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]
                ]
             /\ UNCHANGED<<coordinator>>

\* FOR N PARTICIPANTS

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)


coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB


progN == parProgN \/ coordProgN

\* Death transitions are left outside of fairness

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* CORRECTNESS SPECIFICATION

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants : 
          \/ participant[i].decision # commit 
          \/ participant[j].decision # abort

\* If any participant decides commit, then all participants had votes YES
AC2 == [] (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes)

\* If any participant decides abort then at least one participant voted NO, or
\* there is a faulty participant, or the coordinator is faulty
AC3_1 == [] (\E i \in participants : participant[i].decision = abort)
            => (  (\E j \in participants : participant[j].vote = no)
               \/ (\E j \in participants : participant[j].faulty)
               \/ coordinator.faulty)

\* Each participant decides at most once
AC4 == [] /\ (\A i \in participants : participant[i].decision = commit 
                                => [](participant[i].decision = commit))
          /\ (\A j \in participants : participant[j].decision = abort  
                                => [](participant[j].decision = abort))

\* The original AC5 (termination) does NOT hold for this "simple broadcast"
\* algorithm: some participants may forever be waiting on a broadcast that never
\* arrives.  The model is therefore not "bad": it is just not terminating.
AC5 == <> \A i \in participants : \/ participant[i].decision \in {abort, commit}
                                  \/ participant[i].faulty

====