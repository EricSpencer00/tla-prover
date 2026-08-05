---- MODULE ACP_SB ----
EXTENDS Naturals

CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

TypeInvParticipant ==
  participant \in [ participants ->
    [ vote: {yes, no}, alive: BOOLEAN, decision: {undecided, commit, abort},
      voteSent: BOOLEAN ] ]

TypeInvCoordinator ==
  coordinator \in [ request: [ participants -> BOOLEAN ],
                    vote: [ participants -> {waiting, yes, no} ],
                    decision: {undecided, commit, abort}, alive: BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
  participant \in [ participants ->
    [ vote |-> yes, alive |-> TRUE, decision |-> undecided, voteSent |-> FALSE ] ]

InitCoordinator ==
  coordinator \in [ request |-> [ participants -> FALSE ], vote |-> [ participants -> waiting ],
                    decision |-> undecided, alive |-> TRUE ]

Init == InitParticipant /\ InitCoordinator

\* Coordinator sends vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [ coordinator EXCEPT !.request = [ @ EXCEPT ![i] = TRUE ] ]
  /\ UNCHANGED participant

\* Coordinator records vote from participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [ coordinator EXCEPT !.vote = [ @ EXCEPT ![i] = participant[i].vote ] ]
  /\ UNCHANGED participant

\* Coordinator times out on participant i and decides abort
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [ coordinator EXCEPT !.decision = abort ]
  /\ UNCHANGED participant

\* Coordinator decides commit or abort once all votes are in
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ coordinator' = [ coordinator EXCEPT !.decision = (IF \A j \in participants : coordinator.vote[j] = yes THEN commit ELSE abort) ]
  /\ UNCHANGED participant

\* Coordinator broadcasts its decision to participant i
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [ coordinator EXCEPT !.broadcast = [ @ EXCEPT ![i] = coordinator.decision ] ]
  /\ UNCHANGED participant

\* Coordinator dies
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [ coordinator EXCEPT !.alive = FALSE ]
  /\ UNCHANGED participant

\* Participant i sends its vote
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ participant' = [ participant EXCEPT ![i].voteSent = TRUE ]
  /\ UNCHANGED coordinator

\* Participant i aborts on a no vote
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant[i].decision = undecided
  /\ participant' = [ participant EXCEPT ![i].decision = abort ]
  /\ UNCHANGED coordinator

\* Participant i (still alive) aborts because the coordinator died without a request
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [ participant EXCEPT ![i].decision = abort ]
  /\ UNCHANGED coordinator

\* Participant i decides on coordinator's broadcast
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [ participant EXCEPT ![i].decision = coordinator.broadcast[i] ]
  /\ UNCHANGED coordinator

\* Participant i dies
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [ participant EXCEPT ![i].alive = FALSE ]
  /\ UNCHANGED coordinator

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

coordProg ==
  \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
  \/ makeDecision \/ coordDie

prog == (\E i \in participants : parDie(i) \/ parProg(i)) \/ coordProg

Spec == Init /\ [][prog]_<<coordinator, participant>> /\ WF_<<coordinator, participant>>(coordProg)

\* All participants that decide reach the same decision
AC1 == [] (\A i, j \in participants : participant[i].decision = commit => participant[j].decision # abort)

\* Commit only if all votes are yes
AC2 == [] ( (\E i \in participants : participant[i].decision = commit) =>
            (\A j \in participants : participant[j].vote = yes) )

\* Abort only if some vote is no or some participant/coordinator is faulty
AC3 == [] ( (\E i \in participants : participant[i].decision = abort) =>
            (\E j \in participants : participant[j].vote = no \/ participant[j].faulty) \/ coordinator.faulty )

\* Each participant decides at most once
AC4 == [] (\A i \in participants : participant[i].decision # undecided => [](participant[i].decision = participant[i].decision) )

\* Some participant eventually decides, or some participant/coordinator fails
AC3_2 == <> (\A i \in participants : participant[i].decision # undecided \/ participant[i].faulty) \/ coordinator.faulty

====