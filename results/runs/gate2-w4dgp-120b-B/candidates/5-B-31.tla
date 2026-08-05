---- MODULE ACP_SB ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  participants,             \* set of participants
  yes, no,                  \* vote
  undecided, commit, abort, \* decision
  waiting,                  \* coordinator state wrt a participant
  notsent                   \* broadcast state wrt a participant

VARIABLES
  participant, \* participants (N)
  coordinator  \* coordinator  (1)

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

\* Initially all participants have a yes/no vote, are alive, undecided, and have
\* not sent a vote yet.  The coordinator is alive, undecided, and has not sent
\* vote requests or broadcast messages.

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

\* Coordinator sends a request for a participant's vote
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request =
                   [@ EXCEPT ![i] = TRUE]
                 ]
              /\ UNCHANGED participant

\* Coordinator records a participant's vote, once that participant has sent it
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = 
                   [@ EXCEPT ![i] = participant[i].vote]
                 ]
              /\ UNCHANGED participant

\* Coordinator times out on a dead participant who has not sent its vote
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED participant

\* Coordinator decides once all votes are in
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
                      \/ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED participant

\* Simple broadcast: the coordinator sends its decision to a participant
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = 
                          [@ EXCEPT ![i] = coordinator.decision]
                        ]
                     /\ UNCHANGED participant

\* The coordinator dies and becomes faulty
coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED participant

\* A participant sends its vote to the coordinator
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i] = 
                    [@ EXCEPT !.voteSent = TRUE]
                  ]
               /\ UNCHANGED coordinator

\* A participant unilaterally aborts on a NO vote
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i] = 
                       [@ EXCEPT !.decision = abort]
                     ]
                  /\ UNCHANGED coordinator

\* A participant unilaterally aborts because the coordinator died before
\* sending a request
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i] = 
                                 [@ EXCEPT !.decision = abort]
                               ]
                            /\ UNCHANGED coordinator

\* A participant adopts the coordinator's decision once it receives it
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.decision = coordinator.broadcast[i]]
                ]
             /\ UNCHANGED coordinator

\* A participant dies and becomes faulty
parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = 
                  [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]
                ]
             /\ UNCHANGED coordinator

\* The broadcast primitive is non-terminating, so the protocol's some-safety
\* guarantee is stated as a strong eventuality rather than an absolute one
progN == (\E i \in participants : parDie(i) \/ sendVote(i) \/ abortOnVote(i)
                                 \/ abortOnTimeoutRequest(i) \/ decide(i))
          \/ coordDie \/ makeDecision
          \/ (\E i \in participants : request(i) \/ getVote(i) \/ detectFault(i)
                                      \/ coordBroadcast(i))

fairness == /\ \A i \in participants : WF_<<coordinator, participant>>(sendVote(i))
            /\ \A i \in participants : WF_<<coordinator, participant>>(abortOnVote(i))
            /\ \A i \in participants : WF_<<coordinator, participant>>(abortOnTimeoutRequest(i))
            /\ \A i \in participants : WF_<<coordinator, participant>>(decide(i))
            /\ WF_<<coordinator, participant>>(makeDecision)
            /\ \A i \in participants : WF_<<coordinator, participant>>(coordBroadcast(i))

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: participants that decide all decide the same way, and commit only
\* happens when every vote was YES
AC1 == [] \A i, j \in participants : \/ participant[i].decision # commit
                                  \/ participant[j].decision # abort
AC2 == [] (\E i \in participants : participant[i].decision = commit)
         => (\A j \in participants : participant[j].vote = yes)

\* STRONGER LIVENESS: a decision is eventually reached without any participant
\* having died, since a death can always preempt the decision
AC3 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

====