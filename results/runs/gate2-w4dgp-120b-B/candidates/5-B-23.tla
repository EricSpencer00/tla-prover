---- MODULE ACP_SB ----
EXTENDS Naturals

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
                           vote     : {yes, no}, 
                           alive    : BOOLEAN, 
                           decision : {undecided, commit, abort},
                           faulty   : BOOLEAN,
                           voteSent : BOOLEAN
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

\* Initially all participants are alive and undecided. The coordinator has not
\* sent any request and is undecided. None of the view variables has been set.
Init == /\ participant = ( p1 :> [ vote |-> yes, alive |-> TRUE,
                                    decision |-> undecided, faulty |-> FALSE,
                                    voteSent |-> FALSE ]
                          @@ p2 :> [ vote |-> yes, alive |-> TRUE,
                                    decision |-> undecided, faulty |-> FALSE,
                                    voteSent |-> FALSE ]
                          @@ p3 :> [ vote |-> yes, alive |-> TRUE,
                                    decision |-> undecided, faulty |-> FALSE,
                                    voteSent |-> FALSE ] )
        /\ coordinator = [ request   |-> (p1 :> FALSE @@ p2 :> FALSE @@ p3 :> FALSE),
                           vote      |-> (p1 :> waiting @@ p2 :> waiting @@ p3 :> waiting),
                           broadcast |-> (p1 :> notsent @@ p2 :> notsent @@ p3 :> notsent),
                           decision  |-> undecided,
                           alive     |-> TRUE,
                           faulty    |-> FALSE ]

\* request(i): the coordinator asks participant i for its vote
request(i) == /\ coordinator.alive
              /\ ~coordinator.request[i]
              /\ coordinator' = [coordinator EXCEPT !.request = [@ EXCEPT ![i] = TRUE]]
              /\ UNCHANGED << participant >>

\* getVote(i): the coordinator records the vote of participant i
getVote(i) == /\ coordinator.alive
              /\ coordinator.decision = undecided
              /\ \A j \in participants : coordinator.request[j]
              /\ coordinator.vote[i] = waiting
              /\ participant[i].voteSent
              /\ coordinator' = [coordinator EXCEPT !.vote = [@ EXCEPT ![i] = participant[i].vote]]
              /\ UNCHANGED << participant >>

\* detectFault(i): a participant that has died without voting causes abort
detectFault(i) == /\ coordinator.alive
                  /\ coordinator.decision = undecided
                  /\ \A j \in participants : coordinator.request[j]
                  /\ coordinator.vote[i] = waiting
                  /\ ~participant[i].alive
                  /\ ~participant[i].voteSent
                  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                  /\ UNCHANGED << participant >>

\* makeDecision: once every vote is in, decide commit only if all are yes
makeDecision == /\ coordinator.alive
                /\ coordinator.decision = undecided
                /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
                /\ /\ \A j \in participants : coordinator.vote[j] = yes
                      /\ coordinator' = [coordinator EXCEPT !.decision = commit]
                   \/ /\ \E j \in participants : coordinator.vote[j] = no
                      /\ coordinator' = [coordinator EXCEPT !.decision = abort]
                /\ UNCHANGED << participant >>

\* coordBroadcast(i): simple broadcast of the decision to participant i
coordBroadcast(i) == /\ coordinator.alive
                     /\ coordinator.decision # undecided
                     /\ coordinator.broadcast[i] = notsent
                     /\ coordinator' = [coordinator EXCEPT !.broadcast = [@ EXCEPT ![i] = coordinator.decision]]
                     /\ UNCHANGED << participant >>

\* coordDie: the coordinator fails silently
coordDie == /\ coordinator.alive
            /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
            /\ UNCHANGED << participant >>

\* sendVote(i): a live participant that has been asked sends its vote
sendVote(i) == /\ participant[i].alive
               /\ coordinator.request[i]
               /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
               /\ UNCHANGED << coordinator >>

\* abortOnVote(i): a live participant that voted no aborts immediately
abortOnVote(i) == /\ participant[i].alive
                  /\ participant[i].decision = undecided
                  /\ participant[i].voteSent
                  /\ participant[i].vote = no
                  /\ participant' = [participant EXCEPT ![i].decision = abort]
                  /\ UNCHANGED << coordinator >>

\* abortOnTimeoutRequest(i): a live participant whose coordinator died aborts
abortOnTimeoutRequest(i) == /\ participant[i].alive
                            /\ participant[i].decision = undecided
                            /\ ~coordinator.alive
                            /\ ~coordinator.request[i]
                            /\ participant' = [participant EXCEPT ![i].decision = abort]
                            /\ UNCHANGED << coordinator >>

\* decide(i): a live participant adopts the coordinator's decision
decide(i) == /\ participant[i].alive
             /\ participant[i].decision = undecided
             /\ coordinator.broadcast[i] # notsent
             /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
             /\ UNCHANGED << coordinator >>

\* parDie(i): a participant fails silently
parDie(i) == /\ participant[i].alive
             /\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.alive = FALSE, !.faulty = TRUE]]
             /\ UNCHANGED << coordinator >>

\* A failed participant's vote is never sent, so the coordinator times out and aborts -- 
\* this is the safety failure of the simple broadcast algorithm.
parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

parProgN == \E i \in participants : parDie(i) \/ parProg(i)

coordProgA(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

coordProgB == makeDecision \/ \E i \in participants : coordProgA(i)

coordProgN == coordDie \/ coordProgB

progN == parProgN \/ coordProgN

\* Death transitions are left outside of fairness: they may never happen.
fairness == \A i \in participants : WF_<<coordinator, participant>>(parProg(i))
            /\ WF_<<coordinator, participant>>(coordProgB)

Spec == Init /\ [][progN]_<<coordinator, participant>> /\ fairness

\* SAFETY: all decided participants agree, and commit only when every vote was yes.
AC1 == [] \A i, j \in participants : (participant[i].decision = commit) \/ (participant[j].decision = abort)

AC2 == [] (\E i \in participants : participant[i].decision = commit) => (\A j \in participants : participant[j].vote = yes)

AC3_1 == [] (\E i \in participants : participant[i].decision = abort) =>
          \/ (\E j \in participants : participant[j].vote = no)
             \/ (\E j \in participants : participant[j].faulty)
             \/ coordinator.faulty

AC4 == [] (\A i \in participants : participant[i].decision = commit => [](participant[i].decision = commit))
          /\ (\A i \in participants : participant[i].decision = abort => [](participant[i].decision = abort))

\* LIVENESS: as long as nobody has crashed, everyone eventually decides (or crashes).
AC3_2 == <> (\A i \in participants : participant[i].decision \in {commit, abort} \/ participant[i].faulty)
                 \/ coordinator.faulty

\* Stronger forms used in the proof of AC2 and AC3.
StrongerAC2 == [] (\E i \in participants : participant[i].decision = commit) =>
                 /\ (\A j \in participants : participant[j].vote = yes)
                    /\ coordinator.decision = commit

StrongerAC3_1 == [] (\E i \in participants : participant[i].decision = abort) =>
                    \/ (\E j \in participants : participant[j].vote = no)
                       \/ /\ (\E j \in participants : participant[j].faulty)
                          /\ coordinator.decision = abort
                       \/ /\ coordinator.faulty
                          /\ coordinator.decision = undecided

NoRecovery == [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
                    /\ coordinator.alive <=> ~coordinator.faulty

====